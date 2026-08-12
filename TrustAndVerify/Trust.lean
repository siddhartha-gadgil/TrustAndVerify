import Lean
import TrustAndVerify.TrustExt
open Std
open Lean Elab Term Command Tactic

syntax commandSeq := sepBy1IndentSemicolon(command)

namespace TrustAndVerify

variable [Monad m] [MonadQuotation m]
def toCommandSeq : Array (TSyntax `command) → m (TSyntax `commandSeq)
  | cs => `(commandSeq| $cs*)

def commands : TSyntax `commandSeq → Array (TSyntax `command)
  | `(commandSeq| $cs*) => cs
  | _ => #[]
/--
A class wrapping a proposition `P` that we trust to be true. This allows us to use `P` in proofs without having to provide a proof of `P`. The `elim` field provides a way to extract the proposition `P` from the `Trusted P` instance.

This is like Mathlib's `Fact` class and is duplicated to avoid a dependency on Mathlib.
-/
class Trusted (P : Prop) where
  elim : P

attribute [grind .] Trusted.elim

section
variable (P : Prop)

theorem weHaveP [Trusted P] : P := by grind
end

-- Should also include a variable for the instance if we do not prove. However, we do not want a clash if we implement.
macro "trust" p:term "as" n:ident : command => do
    `(command| theorem $n [Trusted $p] : $p := by grind)

macro "prove"  p:term ":=" pf:term : command => do
    `(command| instance : Trusted $p :=⟨$pf⟩)

macro "use" p:term : command => do
    `(command| variable [Trusted $p])

def transformTerms (transforms: HashMap Expr Expr) (e: Expr) : MetaM Expr := do
  Meta.transform e (post := fun subExpr => do
    match transforms.get? subExpr with
    | some newExpr => return .done newExpr
    | none => return .continue
  )

def transformTerms' (transforms: HashMap Expr Expr) (e: Expr) : MetaM Expr := do
  Meta.transform e (pre := fun subExpr => do
    match transforms.get? subExpr with
    | some newExpr => return .done newExpr
    | none => return .continue
  )


def delabDetailed (e: Expr) : MetaM Syntax.Term := withOptions (fun o₁ =>
                    let o₂ := pp.motives.pi.set o₁ true
                    let o₃ := pp.numericTypes.set o₂ true
                    let o₅ := pp.deepTerms.set o₃ true
                    let o₆ := pp.funBinderTypes.set o₅ true
                    let o₇ := pp.piBinderTypes.set o₆ true
                    let o₈ := pp.letVarTypes.set o₇ true
                    let o₉ := pp.coercions.types.set o₈ true
                    let o' := pp.motives.nonConst.set o₉ true
                    let o'' := pp.fullNames.set o' true
                    pp.unicode.fun.set o'' true) do
              PrettyPrinter.delab e

trust P as go

trust (2 + 2 = 4) as obvious

use 2 + 2 = 4

example : 2 + 2 = 4 := obvious

prove 2 + 2 = 4 := by
    grind

#check go

/--
error: failed to synthesize
  Trusted P

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example : P := by
    apply go

section

use P

example : P := by
    apply go

end

prove P := sorry

example : P := by
    apply go

variable [trustP : Trusted P]

#synth Trusted P


open Lean

#check Meta.kabstract

#check Meta.transform

#check Core.transform

#check Expr.replace





variable (n: Nat)

/-- error: invalid declaration name `n`, there is a section variable with the same name -/
#guard_msgs in
def n: Nat := 1

def transformDefIOtoId (name newName: Name) : MetaM Syntax.Command := do
  -- Create two arbitrary local constants for illustration
  let sourceTerm := Lean.mkConst ``IO
  let targetTerm := Lean.mkConst ``Id

  let ident := mkIdent name
  let fullName ← resolveGlobalConstNoOverload <| ← `($ident)
  let decl := ← getConstInfo fullName
  let typeExpr := decl.type
  let valueExpr := decl.value?.getD (Lean.mkConst ``Unit)
  let m := HashMap.ofList [(sourceTerm, targetTerm)]
  let newTypeExpr ← transformTerms' m typeExpr
  let newValueExpr ← transformTerms' m valueExpr
  let newId := mkIdent newName
  let newTypeSyntax ← delabDetailed newTypeExpr
  let newValueSyntax ← delabDetailed newValueExpr
  let cmd ← `(command| noncomputable def $newId : $newTypeSyntax := $newValueSyntax)
  return cmd

open Lean Meta Elab Term Command Tactic
def eg (n: Nat) : IO Nat := do
    return n + 1

syntax (name := transformIOtoId) "abstract" ident "as" ident : command

@[command_elab transformIOtoId]
def elabTransformIOtoId : CommandElab :=
  fun stx =>
    match stx with
    | `(abstract $name:ident as $newName:ident) => do
        let command ← liftTermElabM  do
            let cmd ← transformDefIOtoId name.getId newName.getId
            TryThis.addSuggestion stx cmd
            pure cmd
        elabCommand command
    | _ => throwUnsupportedSyntax

abstract eg as egAbs

#check egAbs

example (n: Nat) : egAbs (egAbs n) = n + 2 := by
    rfl

-- From Gemini
open Meta
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
