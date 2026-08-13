import TrustAndVerify.Trust
import TrustAndVerify.TrustExt
import TrustAndVerify.Doppelganger

set_option linter.unusedSectionVars false

namespace TrustAndVerify

namespace Examples

section

variable (P: Prop)

theorem weHaveP [Trusted P] : P := by grind
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

prove P := sorry

example : P := by
    apply go

variable [trustP : Trusted P]

#synth Trusted P

def eg (n: Nat) : IO Nat := do
    return n + 1

abstract eg as egAbs

#check egAbs

example (n: Nat) : egAbs (egAbs n) = n + 2 := by
    rfl



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
