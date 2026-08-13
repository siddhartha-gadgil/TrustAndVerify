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
