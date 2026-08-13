import TrustAndVerify.IOLift

open Lean
open Lean.Meta

namespace IOLiftTests

opaque externalPure : Nat → Nat → Nat
opaque externalIO : Nat → Nat → IO Nat

def nestedPure (n : Nat) : Nat :=
  externalPure (externalPure n 1) (externalPure n 2) + 3

def nestedIO (n : Nat) : IO Nat := do
  let left ← externalIO n 1
  let right ← externalIO n 2
  let result ← externalIO left right
  pure (result + 3)

def letPure (n : Nat) : Nat :=
  let first := externalPure n 1
  externalPure first 2

def letIO (n : Nat) : IO Nat :=
  externalIO n 1 >>= fun first =>
  externalIO first 2 >>= fun second =>
  pure second

def partialExternal (n : Nat) : Nat → Nat :=
  externalPure n

def externalCallback (xs : List Nat) : List Nat :=
  xs.map fun n => externalPure n 1

def externalMatch (n : Nat) : Nat :=
  match n with
  | 0 => externalPure 0 1
  | n + 1 => externalPure n 2

def externalConditional (condition : Bool) (n : Nat) : Nat :=
  if condition then externalPure n 1 else externalPure n 2

private def config : IOLift.Config where
  externals := #[{
    pureFn := mkConst ``externalPure
    ioFn := mkConst ``externalIO
  }]

private def definitionValue (name : Name) : MetaM Expr := do
  let info ← getConstInfo name
  let some value := info.value?
    | throwError "expected {name} to be a definition"
  return value

private def assertDefEq (actual expected : Expr) (label : String) : MetaM Unit := do
  unless ← isDefEq actual expected do
    throwError
      "{label} did not produce the expected IO program\nactual:{indentExpr actual}\nexpected:{indentExpr expected}"

private def expectFailure {α} (label : String) (action : MetaM α) : MetaM Unit := do
  let failed ←
    try
      let _ ← action
      pure false
    catch _ =>
      pure true
  unless failed do
    throwError "expected stage-one lifting to reject {label}"

run_meta do
  let nested ← IOLift.liftLambdaBody config (← definitionValue ``nestedPure)
  assertDefEq nested (← definitionValue ``nestedIO) "nested calls"

  let withLet ← IOLift.liftLambdaBody config (← definitionValue ``letPure)
  assertDefEq withLet (← definitionValue ``letIO) "a nondependent let"

  expectFailure "a partial external application" <|
    IOLift.liftLambdaBody config (← definitionValue ``partialExternal)

  expectFailure "an effectful higher-order callback" <|
    IOLift.liftLambdaBody config (← definitionValue ``externalCallback)

  expectFailure "a match expression" <|
    IOLift.liftLambdaBody config (← definitionValue ``externalMatch)

  expectFailure "a conditional" <|
    IOLift.liftLambdaBody config (← definitionValue ``externalConditional)

/- The replacement table can map local parameters, not only constants. -/
run_meta do
  let nat := mkConst ``Nat
  let pureCodomain ← mkArrow nat nat
  let pureType ← mkArrow nat pureCodomain
  let ioCodomain ← mkArrow nat (IOLift.mkIOType nat)
  let ioType ← mkArrow nat ioCodomain

  withLocalDeclD `f pureType fun pureFn =>
    withLocalDeclD `fIO ioType fun ioFn =>
      withLocalDeclD `n nat fun n => do
        let inner := mkAppN pureFn #[n, mkNatLit 1]
        let body := mkAppN pureFn #[inner, mkNatLit 2]
        let localConfig : IOLift.Config := {
          externals := #[{ pureFn, ioFn }]
        }
        let lifted ← IOLift.liftTopChecked localConfig body
        let liftedType ← inferType lifted
        unless ← isDefEq liftedType (IOLift.mkIOType nat) do
          throwError "local replacement produced the wrong type:{indentExpr liftedType}"
        if localConfig.containsExternal lifted then
          throwError "local pure external function remains after lifting:{indentExpr lifted}"

end IOLiftTests
