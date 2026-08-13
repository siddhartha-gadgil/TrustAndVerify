# Expression-Level Lifting of Pure Lean Code to `IO`

## Goal

Suppose verification is carried out on an ordinary pure Lean definition such as:

```lean
def g (f : Nat → Nat → Nat) (n : Nat) : Nat :=
  f (f n 1) 2 + 3
```

At runtime, the implementation of `f` is external:

```lean
fIO : Nat → Nat → IO Nat
```

The goal is to generate an execution-only definition:

```lean
def gIO (fIO : Nat → Nat → IO Nat) (n : Nat) : IO Nat := do
  let a ← fIO n 1
  let b ← fIO a 2
  pure (b + 3)
```

The original `g` remains transparent, pure, and convenient for automated verification with tactics such as `grind`. The generated `gIO` is compiler output and is not intended to be used in theorem statements.

## Overall architecture

There are three layers:

1. **Pure verified definition**: the user writes and proves properties about `g`.
2. **Expression transformer**: an elaborated body `Expr` is transformed into an expression returning `IO`.
3. **Generated declaration**: a command elaborator installs `gIO` with the transformed body.

The central transformation has continuation-passing style:

```lean
lift : Expr → (Expr → MetaM Expr) → MetaM Expr
```

If `e : α`, then:

```lean
lift e k
```

generates an `IO` expression that evaluates `e`, including any external calls, and passes the resulting ordinary value `v : α` to `k`.

The public entry point closes the transformation with `IO.pure`:

```lean
liftTop : Expr → MetaM Expr
```

Conceptually:

```lean
liftTop e = lift e (fun value => pure value)
```

## Why continuation-passing style is useful

An external call cannot be placed directly where its pure result is expected:

```lean
fIO x y : IO Nat
```

must become:

```lean
fIO x y >>= fun value =>
  -- use value : Nat
```

For an ordinary application:

```lean
h a b
```

the transformation is:

```text
lift (h a b) k =
  lift a (fun a' =>
    lift b (fun b' =>
      k (h a' b')))
```

For an external application:

```text
lift (f a b) k =
  lift a (fun a' =>
    lift b (fun b' =>
      bind (fIO a' b') k))
```

The recursive translator `lift` and the continuation `k` have different roles:

- `lift` inspects and transforms an expression;
- `k` constructs what should happen after the current expression produces a value.

The dispatcher does **not** pass itself as `k`. Individual handlers recursively call `lift` on their subexpressions and construct new continuations such as `fun a' => ...`.

## Initial supported fragment

A robust first version should support:

- atomic expressions;
- direct, saturated calls to designated external functions;
- ordinary first-order applications;
- nondependent `let` expressions;
- lambdas that do not contain external calls, or lambdas handled by a dedicated higher-order rule;
- optionally, selected nonrecursive match expressions.

It should initially reject:

- external calls occurring in types or proofs;
- effectful propositions, including conditions such as `if f x = 0 then ...`;
- external calls inside arbitrary higher-order callbacks such as `List.map (fun x => f x x)`;
- dependent matches whose motives must change;
- recursive recursors until recursive-result binders and motive changes are implemented;
- partial applications of an external function;
- escaping external functions, for example returning `f` as a value.

Rejecting unsupported terms is preferable to generating plausible but incorrectly sequenced code.

## Imports and basic types

```lean
import Lean

open Lean
open Lean.Meta

namespace IOLift

abbrev Kont := Expr → MetaM Expr

structure ExternalReplacement where
  /-- The function head occurring in the elaborated pure expression. -/
  pureFn : Expr
  /-- The corresponding function head returning `IO`. -/
  ioFn : Expr

structure Config where
  externals : Array ExternalReplacement := #[]
```

The replacement table may contain constants, free variables, or a mixture. For example, while transforming a body under local binders:

```lean
{
  pureFn := pureFVar,
  ioFn   := ioFVar
}
```

## Recognizing designated external calls

Applications should be decomposed using `getAppFn` and `getAppArgs`.

```lean
def Config.findExternal? (cfg : Config) (fn : Expr) : Option Expr :=
  match cfg.externals.find? (fun replacement => replacement.pureFn == fn) with
  | some replacement => some replacement.ioFn
  | none => none
```

This is more reliable than comparing source-level names because elaboration has already resolved namespaces, shadowing, notation, and overloads.

For the first version, recognize external calls only when the designated function is the complete application head:

```lean
def externalCall? (cfg : Config) (e : Expr) : Option (Expr × Array Expr) :=
  let fn := e.getAppFn
  cfg.findExternal? fn |>.map fun ioFn => (ioFn, e.getAppArgs)
```

The transformer should separately check that the application is saturated according to the interface expected by `ioFn`.

## Building `IO.pure` and `IO.bind`

Lean provides `Meta.mkPure`:

```lean
def mkPureIO (value : Expr) : MetaM Expr :=
  mkPure (mkConst ``IO) value
```

A schematic `bind` builder is:

```lean
def mkIOBind
    (action : Expr)
    (k : Kont) : MetaM Expr := do
  let actionType ← inferType action

  unless actionType.isAppOfArity ``IO 1 do
    throwError "expected an IO action, found type:{indentExpr actionType}"

  let valueType := actionType.getAppArgs[0]!

  withLocalDeclD `value valueType fun value => do
    let body ← k value
    let continuation ← mkLambdaFVars #[value] body
    mkAppM ``bind #[action, continuation]
```

Depending on the Lean version and preferred spelling, `Bind.bind` can be used instead of the root alias `bind`.

## Separating explicit and implicit arguments

Use:

```lean
getFunInfoNArgs fn args.size
```

rather than plain `getFunInfo`, because applications may be partially or over-applied. The returned `FunInfo.paramInfo` aligns parameter information with the supplied arguments.

Relevant fields and predicates include:

```lean
param.binderInfo
param.isExplicit
param.isImplicit
param.isInstImplicit
param.isStrictImplicit
param.isProp
param.hasFwdDeps
param.backDeps
```

It is useful to compute both:

- all arguments, preserving implicit arguments in their original positions;
- only the explicit arguments, for rebuilding with `mkAppM'`.

```lean
structure LiftedArgs where
  full : Array Expr
  explicit : Array Expr
```

The argument transformation is itself continuation-passing:

```lean
partial def liftArgs
    (lift : Expr → Kont → MetaM Expr)
    (fn : Expr)
    (args : Array Expr)
    (k : LiftedArgs → MetaM Expr) : MetaM Expr := do
  let info ← getFunInfoNArgs fn args.size

  unless info.paramInfo.size == args.size do
    throwError "parameter information does not align with application arguments"

  let rec loop
      (i : Nat)
      (full : Array Expr)
      (explicit : Array Expr) : MetaM Expr := do
    if h : i < args.size then
      let arg := args[i]
      let param := info.paramInfo[i]

      if param.isExplicit then
        if param.isProp then
          -- Proof-valued arguments are preserved in the first implementation.
          loop (i + 1) (full.push arg) (explicit.push arg)
        else
          lift arg fun arg' =>
            loop (i + 1) (full.push arg') (explicit.push arg')
      else
        -- Preserve implicit, strict-implicit, and instance arguments.
        loop (i + 1) (full.push arg) explicit
    else
      k { full, explicit }

  loop 0 #[] #[]
```

This version takes `lift` as an ordinary recursion argument so it can also be reused from a mutually recursive implementation.

## Rebuilding applications

There are two useful rebuilding policies.

### Policy A: preserve implicit arguments

For an ordinary pure application, preserve all original implicit and instance arguments:

```lean
let rebuilt := mkAppN fn liftedArgs.full
```

This is generally the safer policy because it avoids resynthesizing instances or implicit parameters that were originally inferred using an expected type.

### Policy B: reconstruct implicit arguments

When the function head has changed, as with `f` becoming `fIO`, rebuild from explicit arguments:

```lean
let rebuilt ← mkAppM' ioFn liftedArgs.explicit
```

`mkAppM'` takes an arbitrary expression-valued function head. `mkAppM` takes a constant name.

This policy assumes that:

- `f` and `fIO` have the same explicit input interface;
- the implicit inputs of `fIO` can be inferred from the explicit inputs;
- no crucial implicit input is determined only by the expected result type;
- resynthesizing a typeclass instance is acceptable.

When only selected implicit arguments should be reconstructed, use `mkAppOptM'` and pass `none` at precisely those positions.

## Dispatcher and handlers

The main function is a prioritized dispatcher. Specialized application forms must be recognized before the generic application case because elaborated conditionals, matchers, recursors, and projections are also applications.

The following is a reference skeleton. Unsupported cases deliberately throw errors.

```lean
mutual
  partial def lift
      (cfg : Config)
      (e : Expr)
      (k : Kont) : MetaM Expr := do

    -- Matchers and recursors must be recognized before generic applications.
    if ← isMatcherApp e then
      liftMatcher cfg e k

    else if let some ioFn := cfg.findExternal? e.getAppFn then
      liftExternalApplication cfg e ioFn k

    else
      match e with
      | .app .. =>
          liftOrdinaryApplication cfg e k

      | .letE _ _ value body _ =>
          lift value fun value' =>
            lift (body.instantiate1 value') k

      | .lam .. =>
          throwError
            "external lifting under arbitrary lambdas is not supported yet:{indentExpr e}"

      | .forallE .. =>
          throwError
            "external lifting in types is not supported:{indentExpr e}"

      | _ =>
          k e

  partial def liftOrdinaryApplication
      (cfg : Config)
      (e : Expr)
      (k : Kont) : MetaM Expr := do
    let fn := e.getAppFn
    let args := e.getAppArgs

    liftArgs (lift cfg) fn args fun liftedArgs => do
      let rebuilt := mkAppN fn liftedArgs.full
      k rebuilt

  partial def liftExternalApplication
      (cfg : Config)
      (e ioFn : Expr)
      (k : Kont) : MetaM Expr := do
    let pureFn := e.getAppFn
    let args := e.getAppArgs

    liftArgs (lift cfg) pureFn args fun liftedArgs => do
      let action ← mkAppM' ioFn liftedArgs.explicit
      mkIOBind action k

  partial def liftMatcher
      (_cfg : Config)
      (e : Expr)
      (_k : Kont) : MetaM Expr := do
    throwError
      "match/recursor lifting is not implemented yet:{indentExpr e}"
end
```

The exact matcher recognizer can be written using:

```lean
matchMatcherApp? e
```

or, when appropriate:

```lean
matchMatcherApp? e (alsoCasesOn := true)
```

rather than treating matchers as arbitrary constant applications.

## The final `Expr → MetaM Expr` entry point

Close the CPS transformation using `IO.pure`:

```lean
def liftTop
    (cfg : Config)
    (e : Expr) : MetaM Expr :=
  lift cfg e mkPureIO
```

Equivalently:

```lean
def liftTop'
    (cfg : Config) : Expr → MetaM Expr :=
  fun e =>
    lift cfg e fun value =>
      mkPure (mkConst ``IO) value
```

This is the function of shape:

```lean
Expr → MetaM Expr
```

needed to transform a definition body.

## Checked top-level entry point

The generated result should be type-checked immediately.

```lean
def mkIOType (α : Expr) : Expr :=
  mkApp (mkConst ``IO) α

def liftTopChecked
    (cfg : Config)
    (e : Expr) : MetaM Expr := do
  let α ← inferType e

  if ← isProp α then
    throwError "cannot lift a proof-valued expression into IO"

  let result ← liftTop cfg e
  let result ← instantiateMVars result

  let actualType ← inferType result
  let expectedType := mkIOType α

  unless ← isDefEq actualType expectedType do
    throwError
      "lifted expression has type:{indentExpr actualType}\n\
       expected:{indentExpr expectedType}"

  ensureHasNoMVars result
  return result
```

This check catches many errors in argument classification, application reconstruction, and bind construction.

## Example translation

Suppose the elaborated expression represents:

```lean
f (f x 1) (f x 2) + 3
```

and the configuration maps the free variable representing `f` to the free variable representing `fIO`.

The CPS translation proceeds conceptually as follows:

```text
lift (f (f x 1) (f x 2) + 3) pure

= lift (f x 1) (fun a =>
    lift (f x 2) (fun b =>
      bind (fIO a b) (fun c =>
        pure (c + 3))))
```

The resulting program is equivalent to:

```lean
do
  let a ← fIO x 1
  let b ← fIO x 2
  let c ← fIO a b
  pure (c + 3)
```

The generated code has an explicit left-to-right evaluation order. That order should be documented as part of the transformation semantics.

## Transforming a nonrecursive declaration body

If `value` is an elaborated lambda expression whose local binder types are already appropriate for the generated declaration, a nonrecursive body can be transformed by telescoping its lambdas:

```lean
def liftLambdaBody
    (cfg : Config)
    (value : Expr) : MetaM Expr := do
  lambdaTelescope value fun xs body => do
    let body' ← liftTopChecked cfg body
    mkLambdaFVars xs body'
```

However, the actual application changes a parameter type:

```lean
f   : Nat → Nat → Nat
fIO : Nat → Nat → IO Nat
```

Therefore one usually cannot reuse the original `f` binder unchanged. The declaration generator must:

1. construct the new function type;
2. introduce fresh local binders for that new type;
3. map old ordinary binders to corresponding new binders;
4. map the old `f` binder to the new `fIO` binder in `Config.externals`;
5. replace old free variables in the body where appropriate;
6. call `liftTopChecked` in the new local context;
7. abstract the new binders with `mkLambdaFVars`;
8. install the generated declaration.

The expression transformer and the declaration generator should be kept separate. The transformer assumes it is given expressions meaningful in its current local context.

## `let` expressions

For a nondependent `let`:

```lean
let x := value
body
```

the simple rule is:

```text
lift (let x := value; body) k =
  lift value (fun value' =>
    lift (body[x := value']) k)
```

At the `Expr` level:

```lean
| .letE _ _ value body _ =>
    lift cfg value fun value' =>
      lift cfg (body.instantiate1 value') k
```

For dependent lets, preserving the let binder may be necessary. The first implementation may reject them or normalize only nondependent lets.

## Conditionals

Lean conditionals are dependent on a proposition and a `Decidable` instance. An expression such as:

```lean
if f x = 0 then t else u
```

contains the external call inside the proposition defining the condition. This is not handled correctly by merely transforming explicit computational arguments.

For the first implementation, reject external calls occurring in the condition proposition or its `Decidable` instance.

Later, a dedicated conditional translation may normalize the data needed by the test first and then reconstruct a pure proposition. For example:

```lean
do
  let y ← fIO x
  if y = 0 then
    liftedT
  else
    liftedU
```

This requires recognizing how the proposition depends on the external call; it is more than generic application lifting.

## Higher-order functions

The generic transformation cannot correctly turn:

```lean
xs.map (fun x => f x x)
```

into effectful code. The intended result uses `mapM`:

```lean
xs.mapM (fun x => fIO x x)
```

Possible extensions include:

- an explicit table of monadic counterparts such as `List.map ↦ List.mapM`;
- user attributes registering higher-order lifting rules;
- an intermediate DSL representing effects;
- syntax-level markers for effectful callbacks.

Until such rules exist, reject lambdas containing designated external calls.

## Match expressions and recursors

After elaboration, `match` is represented using generated matcher functions or recursors. Use Lean's metadata APIs rather than identifying these applications manually:

```lean
matchMatcherApp? e
```

This returns a `MatcherApp` separating:

```lean
matcherName
matcherLevels
params
motive
discrs
altNumParams
alts
remaining
```

and the expression can be rebuilt with:

```lean
matcherApp.toExpr
```

For a first nonrecursive matcher implementation:

1. transform computational discriminants left-to-right;
2. preserve parameters and indices;
3. transform each alternative body to return `IO`;
4. change or reconstruct the motive to return `IO`;
5. preserve remaining over-application arguments;
6. type-check the rebuilt matcher.

For ordinary recursors, `RecursorInfo` provides:

```lean
info.motivePos
info.majorPos
info.isMinor pos
info.numMinors
info.recursive
```

When only the motive should be reconstructed, use `mkAppOptM'`, preserving most arguments and placing `none` only at the motive position.

## Why recursion is the hardest part

For a recursive recursor, changing the motive from:

```lean
A n
```

to:

```lean
IO (A n)
```

also changes recursive-result arguments in minor premises. A branch that originally has an argument:

```lean
recursiveResult : A n
```

will instead receive:

```lean
recursiveAction : IO (A n)
```

The transformed branch must bind this action before using its value:

```lean
fun n recursiveAction => do
  let recursiveResult ← recursiveAction
  -- transformed original branch
```

Thus recursion requires all of the following:

- identify recursive-result binders in each minor premise;
- change their types through the new motive;
- bind them at the beginning of the transformed branch;
- replace uses of the old recursive result by the bound ordinary value;
- reconstruct or infer the new motive;
- rebuild the recursor application with correct parameters, indices, and major premise.

Simply applying `mkAppM'` to the transformed explicit arguments will not by itself insert these binds.

## Recommended recursor rebuilding policy

For an ordinary application:

```lean
mkAppN fn transformedFullArgs
```

For a replaced external function:

```lean
mkAppM' ioFn transformedExplicitArgs
```

For a matcher or recursor:

1. preserve parameters, indices, instances, and proofs;
2. deliberately transform discriminants and minor premises;
3. omit only the motive using `mkAppOptM'` when it should be inferred;
4. check the resulting type immediately.

This is safer than discarding all implicit arguments and asking Lean to reconstruct everything.

## Validation checklist

Every generated body should be checked with:

```lean
let result ← instantiateMVars result
let resultType ← inferType result
ensureHasNoMVars result
```

Additionally verify:

- the result type is definitionally equal to the intended `IO` type;
- no designated pure external function remains in the generated term;
- external functions are fully applied;
- no external call occurs in a proof or type;
- no unsupported lambda contains an external call;
- evaluation order is deterministic and documented;
- the generated declaration passes the kernel type checker;
- compiler errors identify the original unsupported subexpression.

It is also useful to pretty-print generated code during development:

```lean
logInfo m!"generated IO expression:{indentExpr result}"
```

## Semantic boundary

The transformation establishes how the pure algorithm's calls are sequenced in `IO`. It does not prove that the external implementation agrees with the pure specification.

Properties proved about:

```lean
g f
```

apply to execution with `gIO fIO` only under a contract relating `fIO` to `f`. Depending on the application, this contract may state that:

- every successful call to `fIO x y` returns `f x y`;
- the call may fail but cannot return an incorrect result;
- mutable external state satisfies an invariant;
- nondeterministic results satisfy a pure relation rather than equal a single pure value.

If failure, state, or nondeterminism is semantically important, the pure specification may need an explicit model such as `Except`, `StateM`, or a custom command/result relation.

## Suggested implementation stages

### Stage 1

- nonrecursive functions;
- direct saturated external calls;
- atomic expressions, ordinary applications, and nondependent lets;
- left-to-right sequencing;
- strict rejection of unsupported terms;
- final type and metavariable checks.

### Stage 2

- selected nonrecursive matchers;
- explicit reconstruction of motives;
- better error messages with source information;
- tests for implicit arguments and local instances.

### Stage 3

- structural recursion;
- identification and binding of recursive actions;
- mutual recursion if required;
- generated correspondence tests using pure mock implementations.

### Stage 4

- registered higher-order lifting rules such as `map ↦ mapM`;
- modeled failure and state;
- runtime or formal contracts for external implementations.

## Relevant Lean APIs

- `Expr.getAppFn`, `Expr.getAppArgs`, `mkAppN`
- `Meta.getFunInfoNArgs`, `FunInfo.paramInfo`, `ParamInfo.isExplicit`
- `Meta.mkAppM`, `Meta.mkAppM'`, `Meta.mkAppOptM`, `Meta.mkAppOptM'`
- `Meta.mkPure`
- `Meta.inferType`, `Meta.isDefEq`, `Meta.instantiateMVars`
- `Meta.ensureHasNoMVars`
- `Meta.lambdaTelescope`, `Meta.mkLambdaFVars`
- `Meta.matchMatcherApp?`, `MatcherApp.toExpr`
- `Meta.mkRecursorInfo`, `RecursorInfo`

Official API references:

- <https://lean-lang.org/doc/api/Lean/Meta/FunInfo.html>
- <https://lean-lang.org/doc/api/Lean/Meta/AppBuilder.html>
- <https://lean-lang.org/doc/api/Lean/Meta/RecursorInfo.html>

If the snippets are assembled into one Lean module, finish it with:

```lean
end IOLift
```
