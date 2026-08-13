import Lean

open Lean
open Lean.Meta

/-!
# Expression-level lifting of pure code to `IO`

This module implements stage one of `lean_io_expression_lifting_design.md`.  It
translates the supported, first-order fragment in continuation-passing style.
Designated external calls are sequenced from left to right; every other
supported computation stays pure.

Matchers, recursors, effectful conditions, dependent lets, effectful
higher-order callbacks, partial external applications, and escaping external
functions are rejected deliberately.  Declaration generation is a separate
layer: callers construct the replacement table in the local context in which
they invoke `liftTopChecked`.
-/

namespace IOLift

/-- A continuation accepting the pure value produced by a lifted expression. -/
abbrev Kont := Expr → MetaM Expr

/-- A pure function head and the corresponding function head returning `IO`. -/
structure ExternalReplacement where
  pureFn : Expr
  ioFn : Expr

/-- Configuration for one lifting run. -/
structure Config where
  externals : Array ExternalReplacement := #[]

/-- Find the `IO` implementation registered for an elaborated function head. -/
def Config.findExternal? (cfg : Config) (fn : Expr) : Option Expr :=
  match cfg.externals.find? (fun replacement => replacement.pureFn == fn) with
  | some replacement => some replacement.ioFn
  | none => none

private partial def containsExpr (e target : Expr) : Bool :=
  if e == target then
    true
  else
    match e with
    | .app fn arg => containsExpr fn target || containsExpr arg target
    | .lam _ type body _ => containsExpr type target || containsExpr body target
    | .forallE _ type body _ => containsExpr type target || containsExpr body target
    | .letE _ type value body _ =>
        containsExpr type target || containsExpr value target || containsExpr body target
    | .mdata _ body => containsExpr body target
    | .proj _ _ value => containsExpr value target
    | _ => false

/-- Return whether an expression contains a registered pure external function. -/
def Config.containsExternal (cfg : Config) (e : Expr) : Bool :=
  cfg.externals.any fun replacement => containsExpr e replacement.pureFn

/-- Recognize a direct application whose complete head is registered. -/
def externalCall? (cfg : Config) (e : Expr) : Option (Expr × Array Expr) :=
  cfg.findExternal? e.getAppFn |>.map fun ioFn => (ioFn, e.getAppArgs)

/-- The original arguments in their positions and their explicit subsequence. -/
structure LiftedArgs where
  full : Array Expr
  explicit : Array Expr

/-- Construct `IO.pure value`. -/
def mkPureIO (value : Expr) : MetaM Expr :=
  mkPure (mkConst ``IO) value

/--
Construct an `IO.bind`, exposing the action's ordinary result to `k`.

Checking the action type here is also the saturation check for replacements:
after all supplied explicit arguments have been applied, an external
implementation must have type `IO α`, not another function type.
-/
def mkIOBind (action : Expr) (k : Kont) : MetaM Expr := do
  let actionType ← instantiateMVars (← inferType action)

  unless actionType.isAppOfArity ``IO 1 do
    throwError
      "external implementation must be fully applied and return IO; found type:{indentExpr actionType}"

  let valueType := actionType.getAppArgs[0]!
  withLocalDeclD `value valueType fun value => do
    let body ← k value
    let continuation ← mkLambdaFVars #[value] body
    mkAppM ``Bind.bind #[action, continuation]

private def ensureExternalFree
    (cfg : Config)
    (e : Expr)
    (location : String) : MetaM Unit := do
  if cfg.containsExternal e then
    throwError
      "designated external function occurs in {location}, which stage-one IO lifting does not support:{indentExpr e}"

private def ensureTypeExternalFree
    (cfg : Config)
    (e : Expr)
    (location : String) : MetaM Unit := do
  let type ← instantiateMVars (← inferType e)
  ensureExternalFree cfg type s!"the type of {location}"

private def isRecursorApp (e : Expr) : MetaM Bool := do
  match e.getAppFn with
  | .const name _ => isRec name
  | _ => pure false

private def isConditionalApp (e : Expr) : Bool :=
  e.getAppFn.isConstOf ``ite || e.getAppFn.isConstOf ``dite

/--
Lift application arguments from left to right.

Implicit, instance, and proof-valued arguments are preserved exactly.  They
must be external-free because stage one does not transform types or proofs.
-/
partial def liftArgs
    (lift : Expr → Kont → MetaM Expr)
    (cfg : Config)
    (fn : Expr)
    (args : Array Expr)
    (k : LiftedArgs → MetaM Expr) : MetaM Expr := do
  let info ← getFunInfoNArgs fn args.size

  unless info.paramInfo.size == args.size do
    throwError
      "parameter information does not align with application arguments for:{indentExpr (mkAppN fn args)}"

  let rec loop
      (i : Nat)
      (full : Array Expr)
      (explicit : Array Expr) : MetaM Expr := do
    if h : i < args.size then
      let arg := args[i]
      let param := info.paramInfo[i]!

      ensureTypeExternalFree cfg arg "an application argument"

      if param.isExplicit && !param.isProp then
        lift arg fun arg' =>
          loop (i + 1) (full.push arg') (explicit.push arg')
      else
        ensureExternalFree cfg arg "an implicit, instance, or proof argument"
        let explicit := if param.isExplicit then explicit.push arg else explicit
        loop (i + 1) (full.push arg) explicit
    else
      k { full, explicit }

  loop 0 #[] #[]

mutual
  /--
  Lift a supported pure expression and pass its ordinary result to `k`.

  Calls nested in application arguments are evaluated left-to-right.
  -/
  partial def lift (cfg : Config) (e : Expr) (k : Kont) : MetaM Expr := do
    ensureTypeExternalFree cfg e "the expression being lifted"

    if ← isMatcherApp e then
      liftMatcher cfg e k
    else if ← isRecursorApp e then
      throwError "recursor lifting is not implemented in stage one:{indentExpr e}"
    else if isConditionalApp e && cfg.containsExternal e then
      throwError "conditional lifting is not implemented in stage one:{indentExpr e}"
    else if let some ioFn := cfg.findExternal? e.getAppFn then
      liftExternalApplication cfg e ioFn k
    else
      match e with
      | .app .. =>
          liftOrdinaryApplication cfg e k

      | .letE name type value body _ =>
          ensureExternalFree cfg type "a let-binder type"
          withLocalDeclD name type fun letVar => do
            let bodyType ← inferType (body.instantiate1 letVar)
            if bodyType.containsFVar letVar.fvarId! then
              throwError "dependent let lifting is not implemented in stage one:{indentExpr e}"
          lift cfg value fun value' =>
            lift cfg (body.instantiate1 value') k

      | .lam .. =>
          ensureExternalFree cfg e "a lambda or higher-order callback"
          k e

      | .forallE .. =>
          throwError "lifting type expressions is not supported:{indentExpr e}"

      | .mdata data body =>
          lift cfg body fun value => k (.mdata data value)

      | .mvar .. =>
          throwError "cannot lift an expression containing an unresolved metavariable:{indentExpr e}"

      | _ =>
          if cfg.containsExternal e then
            throwError
              "designated external function is partially applied, escapes as a value, or occurs in an unsupported expression:{indentExpr e}"
          k e

  /-- Lift an ordinary pure application, preserving all elaborated arguments. -/
  partial def liftOrdinaryApplication
      (cfg : Config)
      (e : Expr)
      (k : Kont) : MetaM Expr := do
    let fn := e.getAppFn
    let args := e.getAppArgs

    if cfg.containsExternal fn then
      throwError "an external computation occurs in function position:{indentExpr e}"

    liftArgs (lift cfg) cfg fn args fun liftedArgs =>
      k (mkAppN fn liftedArgs.full)

  /-- Lift a direct external call, rebuilding its changed head from explicit arguments. -/
  partial def liftExternalApplication
      (cfg : Config)
      (e ioFn : Expr)
      (k : Kont) : MetaM Expr := do
    let pureFn := e.getAppFn
    let args := e.getAppArgs

    if args.isEmpty then
      throwError "designated external function escapes as a value:{indentExpr e}"

    liftArgs (lift cfg) cfg pureFn args fun liftedArgs => do
      let action ← mkAppM' ioFn liftedArgs.explicit
      mkIOBind action k

  /-- Stage one rejects all generated matchers; stage two will rebuild motives and alternatives. -/
  partial def liftMatcher
      (_cfg : Config)
      (e : Expr)
      (_k : Kont) : MetaM Expr := do
    throwError "match lifting is not implemented in stage one:{indentExpr e}"
end

/-- Close the CPS translation using `IO.pure`. -/
def liftTop (cfg : Config) (e : Expr) : MetaM Expr :=
  lift cfg e mkPureIO

/-- Construct `IO α`. -/
def mkIOType (α : Expr) : Expr :=
  mkApp (mkConst ``IO) α

/--
Lift an expression and immediately check its result type, external-call
elimination, and metavariable closure.
-/
def liftTopChecked (cfg : Config) (e : Expr) : MetaM Expr := do
  let α ← instantiateMVars (← inferType e)

  if ← isProp α then
    throwError "cannot lift a proof-valued expression into IO:{indentExpr e}"

  ensureExternalFree cfg α "the result type"

  let result ← instantiateMVars (← liftTop cfg e)
  let actualType ← instantiateMVars (← inferType result)
  let expectedType := mkIOType α

  unless ← isDefEq actualType expectedType do
    throwError
      "lifted expression has type:{indentExpr actualType}\nexpected:{indentExpr expectedType}"

  let result ← instantiateMVars result
  if result.hasMVar then
    throwError "lifted expression contains unresolved metavariables:{indentExpr result}"

  if cfg.containsExternal result then
    throwError "a designated pure external function remains after lifting:{indentExpr result}"

  return result

/--
Lift the body under an existing lambda telescope.

This helper is for declarations whose binder types do not change.  When a pure
external parameter is replaced by an `IO` parameter, the declaration generator
must instead build the new telescope and configure the old/new free-variable
mapping before calling `liftTopChecked`.
-/
def liftLambdaBody (cfg : Config) (value : Expr) : MetaM Expr := do
  lambdaTelescope value fun xs body => do
    let body' ← liftTopChecked cfg body
    mkLambdaFVars xs body'

end IOLift
