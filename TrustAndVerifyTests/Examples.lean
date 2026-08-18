import TrustAndVerify.Trust
import TrustAndVerify.TrustExt
import TrustAndVerify.Doppelganger

set_option linter.unusedSectionVars false

/-!
# Miscellaneous examples and experiments with the Trust and Verify framework.
-/

namespace TrustAndVerify

namespace Examples

section

variable (P: Prop)

theorem weHaveP [Trusted P] : P := by apply Trusted.elim
end

trust (2 + 2 = 4) as obvious

#print obvious

opaque P : Prop

trust P as go

#eval TrustState.viewTrusts

variable (n : Nat)

theorem two_plus_two : 2 + 2 = 4 := obvious

#print two_plus_two

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

variable [t'' :SimplyTrusted <| 2 + 3 = 5]

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

def double' (n: Nat) : Nat := n + n

facade dble of double'

#check dble

#print dble

trust ∀n, dble n = n + n as dbleTrust

@[grind .]
noncomputable def quadrupleId (n: Nat) : Id Nat := return dble (dble n)

#check dbleTrust

theorem quadrupleIdCorrect  (n: Nat): quadrupleId n = pure (n + n + n + n) := by
    grind [dbleTrust]

@[grind .]
noncomputable def quadruple (n: Nat) : Nat := Id.run (quadrupleId n)

theorem quadrupleCorrect (n: Nat): quadruple n = n + n + n + n := by
    grind [dbleTrust]

noncomputable def dbleId : Nat → Id Nat := dble

trust ∀n, dbleId n = pure (n + n) as dbleIdTrust

trust ∀n, Id.run do (← dbleId n) = n + n as dbleIdTrust'

@[grind .]
noncomputable def quadrupleId' (n: Nat) : Id Nat := do
    let x ← dbleId n
    let y ← dbleId x
    return y

#print quadrupleId'

noncomputable def quardrupleId'' (n: Nat) : Nat :=
    let x := dbleId n
    let y := dbleId x
    y

@[grind .]
theorem quadrupleId'Correct  (n: Nat): quadrupleId' n = pure (n + n + n + n) := by
    have h := dbleIdTrust'
    simp at h
    grind [dbleIdTrust]

@[grind .]
noncomputable def quadruple' (n: Nat) : Nat := Id.run (quadrupleId' n)

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

opaque Q : Prop

/--
error: failed to synthesize 'Inhabited' or 'Nonempty' instance for
  Q

If this type is defined using the 'structure' or 'inductive' command, you can try adding a 'deriving Nonempty' clause to it.
-/
#guard_msgs in
opaque x : Q

opaque f : Nat → Nat
#eval f 3 -- 0

noncomputable opaque g : Nat → Nat
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'g', which is 'noncomputable'
-/
#guard_msgs in
#eval g 3 -- 0

/--
error: Tactic `rfl` failed: The left-hand side
  f 3
is not definitionally equal to the right-hand side
  0

inst✝⁶ : SimplyTrusted (2 + 2 = 4)
inst✝⁵ : SimplyTrusted P
n : Nat
t : Trusted P
t'' : SimplyTrusted (2 + 3 = 5)
trustP inst✝⁴ inst✝³ : Trusted P
inst✝² : SimplyTrusted (∀ (n : Nat), dble n = n + n)
inst✝¹ : SimplyTrusted (∀ (n : Nat), dbleId n = pure (n + n))
inst✝ :
  SimplyTrusted
    (∀ (n : Nat),
      (do
          let __do_lift ← dbleId n
          __do_lift = n + n).run)
dc : DoubleClass
⊢ f 3 = 0
-/
#guard_msgs in
example : f 3 = 0 := by rfl


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
  let resultExpr ← transformMappedTerms m pairExpr

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

example : 1/0 = 0/0 := by rfl

example : 1/0 = 0 := by rfl

#eval [1, 2, 3][0]

#eval getElem [1, 2, 3] 0 (by get_elem_tactic_extensible)

@[facade trpl]
def triple (n: Nat) : Nat := n + n + n

#check trpl

#print trpl

@[abstract hi]
def hello : String := "world"

#print hi
