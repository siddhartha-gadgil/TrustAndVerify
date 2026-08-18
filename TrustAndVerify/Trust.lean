import Lean
import TrustAndVerify.TrustExt
import TrustAndVerify.Basic
open Std
open Lean Meta Elab Term Command Tactic

/-!
# Trust and Verify

This module is a framework and associated syntax to use *trusted* propositions in Lean. A trusted proposition is a proposition that we assume to be true without providing a proof. Our primary goal is to *trust* properties of functions that wrap Python functions. This can also be used to trust conjectures.

Our first step is to define a class `Trusted` that wraps a proposition `P` that we trust to be true. This allows us to use `P` in proofs without having to provide a proof of `P`. The `elim` field provides a way to extract the proposition `P` from the `Trusted P` instance. This class is similar to Mathlib's `Fact` class, but we duplicate it here to avoid a dependency on Mathlib. We will add an optional source of trust to the `Trusted` class in the future, so that we can track where the trust comes from. For now, we just have a single field `trust` that is a proof of `P`.

Given this class, we follow a pattern to trust a proposition `P` and then use it in proofs. Suppose, for example, `RH : Prop` is the statement of the Riemann Hypothesis. Suppose we want to work under the assumption that `RH` is true. The pattern we follow is the following:

```lean
theorem riemann_hypothesis [Trusted RH] : RH := by grind
variable [Trusted RH]
```

This means that any consequence of the Riemann Hypothesis can be proved using the `Trusted RH` instance. However, the signature of the consequence will include [Trusted RH] as a parameter.

We introduce a command `trust` that allows us to trust a proposition `P` and give it a name `n`. This will create a theorem `n` that is an instance of `Trusted P`, and also add a variable `[Trusted P]` to the context. For example, we can write
```lean
trust (2 + 2 = 4) as obvious
```
This will create a theorem `obvious` that is an instance of `Trusted (2 + 2 = 4)`, and also add a variable `[Trusted (2 + 2 = 4)]` to the context. We can then use `obvious` in proofs without having to provide a proof of `2 + 2 = 4`. For example, we can write
```lean
example : 2 + 2 = 4 := obvious
```

Since variables are not automatically added to the context, we also provide a command `use_trusted` that will add all trusted propositions to the context.

-/

namespace TrustAndVerify

/--
A class wrapping a proposition `P` that we trust to be true. This allows us to use `P` in proofs without having to provide a proof of `P`. The `elim` field provides a way to extract the proposition `P` from the `Trusted P` instance.

This is like Mathlib's `Fact` class and is duplicated to avoid a dependency on Mathlib. We will add an optional source of trust to the `Trusted` class in the future, so that we can track where the trust comes from. For now, we just have a single field `trust` that is a proof of `P`.
-/
class Trusted (P : Prop) where
  trust : P

class SimplyTrusted (P : Prop) extends Trusted P

@[grind .]
theorem Trusted.elim {P : Prop} [Trusted P] : P := by
  apply Trusted.trust

/--
Trust the proposition `P` and give it a name `n`. This will create a theorem `n` that is an instance of `Trusted P`, and also add a variable `[Trusted P]` to the context.
-/
syntax (name := trustCmd) "trust" term "as" ident : command

@[command_elab trustCmd]
def elabTrust : CommandElab := fun stx => match stx with
  | `(trust $p:term as $n:ident) => do
    let trustIdent := mkIdent ``Trusted
    let simplyTrustIdent := mkIdent ``SimplyTrusted
    let trustElimIdent := mkIdent ``Trusted.elim
    let cmd ← `(command| theorem $n [$trustIdent $p] : $p := by apply $trustElimIdent)
    let cmd' ← `(command| variable [$simplyTrustIdent $p])
    let cmds ← toCommandSeq #[cmd, cmd']
    liftTermElabM do
     TryThis.addSuggestion stx cmds
     TrustState.addTrust n.getId p
    elabCommand cmd
    elabCommand cmd'
  | _ => throwUnsupportedSyntax

def variableCommand (ps : Array (Name × Syntax.Term)) : MetaM (TSyntax `command) := do
  let vars ← ps.mapM fun (_, stx) => do
    let ident := mkIdent ``SimplyTrusted
    `(bracketedBinder|[$ident $stx])
  let cmd ← `(command| variable $vars*)
  return cmd

syntax (name := useCmd) "use_trusted" : command

@[command_elab useCmd]
def elabUseAll : CommandElab := fun stx => match stx with
  | `(use_trusted) => do
    let cmd ← liftTermElabM do
      let env ← getEnv
      let trusts ← TrustState.getTrusts
      let trusts := trusts.filter fun (n, _) =>
        !(env.contains n)
      variableCommand trusts
    liftTermElabM do
     TryThis.addSuggestion stx cmd
    elabCommand cmd
  | _ => throwUnsupportedSyntax

macro "prove"  p:term ":=" pf:term : command => do
    `(command| @[default_instance] instance : Trusted $p :=⟨$pf⟩)
