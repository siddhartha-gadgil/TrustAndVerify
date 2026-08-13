import TrustAndVerify.Trust
import TrustAndVerify.TrustExt
import TrustAndVerify.Doppelganger

set_option linter.unusedSectionVars false

namespace TrustAndVerify

namespace Examples

section

variable (P: Prop)

theorem weHaveP [Trusted P] : P := by apply Trusted.elim
end

trust (2 + 2 = 4) as obvious

opaque P : Prop

trust P as go

#eval TrustState.viewTrusts

example : 2 + 2 = 4 := obvious

prove 2 + 2 = 4 := by
    grind

#check go

example : P := by
    apply go

section


example : P := by
    apply go

end

variable [t :Trusted P]

section

variable [t' : Trusted <| 2 + 3 = 5]

end

@[default_instance]
instance eqn  : Trusted (2 + 3 = 5) := ⟨rfl⟩

#check eqn

#synth Trusted (2 + 3 = 5)

prove P := sorry

instance (priority := 1000) e : Trusted P := by grind

-- variable [tt :Trusted P]

#synth Trusted P

example : P := by
    apply go

variable [trustP : Trusted P]

#synth Trusted P

variable [Trusted P]
variable [Trusted P]

def eg (n: Nat) : IO Nat := do
    return n + 1

abstract eg as egAbs

#check egAbs

example (n: Nat) : egAbs (egAbs n) = n + 2 := by
    rfl


facade dble : Nat → Nat

trust ∀n, dble n = n + n as dbleTrust

@[grind .]
def quadrupleId (n: Nat) : Id Nat := return dble (dble n)

#check dbleTrust

theorem quadrupleIdCorrect  (n: Nat): quadrupleId n = pure (n + n + n + n) := by
    grind [dbleTrust]

@[grind .]
def quadruple (n: Nat) : Nat := Id.run (quadrupleId n)

theorem quadrupleCorrect (n: Nat): quadruple n = n + n + n + n := by
    grind [dbleTrust]

facade dbleId : Nat → Id Nat

trust ∀n, dbleId n = pure (n + n) as dbleIdTrust

trust ∀n, Id.run do (← dbleId n) = n + n as dbleIdTrust'

@[grind .]
def quadrupleId' (n: Nat) : Id Nat := do
    let x ← dbleId n
    let y ← dbleId x
    return y

#print quadrupleId'

def quardrupleId'' (n: Nat) : Nat :=
    let x := dbleId n
    let y := dbleId x
    y

@[grind .]
theorem quadrupleId'Correct  (n: Nat): quadrupleId' n = pure (n + n + n + n) := by
    have h := dbleIdTrust'
    simp at h
    grind [dbleIdTrust]

@[grind .]
def quadruple' (n: Nat) : Nat := Id.run (quadrupleId' n)

theorem quadruple'Correct (n: Nat): quadruple' n = n + n + n + n := by
    grind [dbleIdTrust]

class DoubleClass where
    doubleFn : Nat → Nat

variable [dc : DoubleClass]

def double [dc : DoubleClass](n: Nat) : Nat := dc.doubleFn n


@[default_instance]
instance : DoubleClass where
    doubleFn := fun n => n + n

/-- error: Cannot evaluate, contains free variable `dc` -/
#guard_msgs in
#eval double 5

#synth Monad IO
def IO.flatMap := @bind (m := IO) (inferInstance)
#check IO.flatMap

-- From Gemini
open Lean Meta Std
def transformTermsDemo : MetaM Unit := do
  -- Create two arbitrary local constants for illustration
  let sourceTerm := Lean.mkNatLit 42
  let targetTerm := Lean.mkStrLit "forty-two" -- Changing type from Nat to String

  let m := HashMap.ofList [(sourceTerm, targetTerm)]

  -- Target expression: (42, 42)
  let pairExpr ← mkAppM ``Prod.mk #[sourceTerm, sourceTerm]
  IO.println s!"Original Pair: {← ppExpr pairExpr}"

  -- Transform the expression
  let resultExpr ← transformTerms m pairExpr

  IO.println s!"Transformed Pair: {← ppExpr resultExpr}"

#eval transformTermsDemo

def transformTermsDemo' : MetaM Unit := do
  -- Create two arbitrary local constants for illustration
  let sourceTerm := mkNatLit 42
  let targetTerm := mkStrLit "forty-two" -- Changing type from Nat to String
  let m := HashMap.ofList [(sourceTerm, targetTerm)]

  -- Target expression: (42, 42)
  let pairExpr ← mkAppM ``Prod.mk #[sourceTerm, sourceTerm]
  IO.println s!"Original Pair: {← ppExpr pairExpr}"

  -- Transform the expression
  let resultExpr ← transformTerms' m pairExpr

  IO.println s!"Transformed Pair: {← ppExpr resultExpr}"

#eval transformTermsDemo'

-- from ChatGPT

open Lean Meta

def getExplicitArgs
    (e : Expr) : MetaM (Expr × Array Expr) :=
  e.withApp fun fn args => do
    let info ← getFunInfoNArgs fn args.size

    unless info.paramInfo.size == args.size do
      throwError "unexpected parameter-information size"

    let mut explicitArgs := #[]

    for i in [:args.size] do
      let arg := args[i]!
      let param := info.paramInfo[i]!

      if param.isExplicit then
        explicitArgs := explicitArgs.push arg

    return (fn, explicitArgs)

def mapExplicitArgsM
    (e : Expr)
    (mapArg : Expr → MetaM Expr) :
    MetaM Expr :=
  e.withApp fun fn args => do
    let info ← getFunInfoNArgs fn args.size

    unless info.paramInfo.size == args.size do
      throwError "unexpected parameter-information size"

    let mut newArgs := #[]

    for i in [:args.size] do
      let arg := args[i]!
      let param := info.paramInfo[i]!

      let arg' ←
        if param.isExplicit && !param.isProp then
          mapArg arg
        else
          pure arg

      newArgs := newArgs.push arg'

    return mkAppN fn newArgs

/-!
```
let recInfo ← mkRecursorInfo recursorName

let suppliedArgs : Array (Option Expr) :=
  args.mapIdx fun i arg =>
    if i == recInfo.motivePos then
      none                    -- re-infer changed motive
    else
      some transformedOrOriginalArg

let result ← mkAppOptM' recursorFn suppliedArgs
```
Ref: https://lean-lang.org/doc/api/Lean/Meta/RecursorInfo.html
-/
