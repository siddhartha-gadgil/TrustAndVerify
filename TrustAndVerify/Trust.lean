import Lean
import TrustAndVerify.TrustExt
import TrustAndVerify.Basic
open Std
open Lean Meta Elab Term Command Tactic
set_option linter.unusedSectionVars false

namespace TrustAndVerify

/--
A class wrapping a proposition `P` that we trust to be true. This allows us to use `P` in proofs without having to provide a proof of `P`. The `elim` field provides a way to extract the proposition `P` from the `Trusted P` instance.

This is like Mathlib's `Fact` class and is duplicated to avoid a dependency on Mathlib. We will add an optional source of trust to the `Trusted` class in the future, so that we can track where the trust comes from. For now, we just have a single field `trust` that is a proof of `P`.
-/
class Trusted (P : Prop) where
  trust : P

@[grind .]
theorem Trusted.elim {P : Prop} [Trusted P] : P := by
  apply Trusted.trust

syntax (name := trustCmd) "trust" term "as" ident : command

@[command_elab trustCmd]
def elabTrust : CommandElab := fun stx => match stx with
  | `(trust $p:term as $n:ident) => do
    let trustIdent := mkIdent ``Trusted
    let cmd ← `(command| theorem $n [$trustIdent $p] : $p := by grind)
    let cmd' ← `(command| variable [$trustIdent $p])
    let cmds ← toCommandSeq #[cmd, cmd']
    liftTermElabM do
     TryThis.addSuggestion stx cmds
     TrustState.addTrust n.getId p
    elabCommand cmd
    elabCommand cmd'
  | _ => throwUnsupportedSyntax

def variableComand (ps : Array (Name × Syntax.Term)) : MetaM (TSyntax `command) := do
  let vars ← ps.mapM fun (_, stx) => do
    let ident := mkIdent ``Trusted
    `(bracketedBinder|[$ident $stx])
  let cmd ← `(command| variable $vars*)
  return cmd

syntax (name := useCmd) "use_trusted" : command
@[command_elab useCmd]
def elabUseAll : CommandElab := fun stx => match stx with
  | `(use_trusted) => do
    let cmd ← liftTermElabM do
      let trusts ← TrustState.getTrusts
      variableComand trusts
    liftTermElabM do
     TryThis.addSuggestion stx cmd
    elabCommand cmd
  | _ => throwUnsupportedSyntax

macro "prove"  p:term ":=" pf:term : command => do
    `(command| instance : Trusted $p :=⟨$pf⟩)
