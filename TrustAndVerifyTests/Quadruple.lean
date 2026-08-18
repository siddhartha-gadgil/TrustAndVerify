import TrustAndVerify

namespace TrustAndVerify.Examples

/-!
# Lean inference with external computation and trust

This file contains examples of using Lean's inference engine with external computation and trust. It demonstrates how to define functions that rely on external computation (e.g., Python scripts) and how to **trust** certain propositions to simplify proofs.
-/

/-!
We use here a simple *pipe* that runs a command in Python using `python3 -c` and returns the output. In practice we should use other pipes that work with JSON or some form of FFI (foreign-function interface) to communicate with external programs.
-/
#pipe_python

/-!
## Facades and Trust

In our first example, we define a function `double` that doubles a natural number using an external Python computation. We then trust the proposition that `double n = n + n` for all natural numbers `n`. The attribute `@[facade double]` adds an additional command that introduces an opaque version of `double` that can be used in proofs without revealing the implementation details. In this case this has the same type as `timesTwo`, but in general the type is changed to be more *proof-friendly*, for instance replacing `Float` with `Real`.
-/

/--
Double a natural number using an external Python computation. The `timesTwo` function takes a natural number `n`, sends it to a Python script that computes `n * 2`, and returns the result as a natural number.
-/
@[facade double]
def timesTwo (n : Nat) : Nat :=
    fetch (encode := fun n => s!"print({n})") (decode := fun (s : String) => s.toNat!) n

/-- info: opaque double : Nat → Nat -/
#guard_msgs in
#print double

/-!
The `trust` command allows us to trust the proposition that `double n = n + n` for all natural numbers `n`. The general pattern is to introduce a facade and then trust propositions that characterize the behavior of the facade. This allows us to use the facade in proofs without having to provide a proof of the trusted proposition.
-/
trust ∀ n, double n = n + n as dble_eqn

/-- info: #[(dble_eqn, ∀ n, double n = n + n)] -/
#guard_msgs in
#eval TrustState.viewTrusts

/-!
## Doppelgangers and Abstracting Definitions

Our goal is to build verified code that uses the external definitions. The next ingredient is to define a *doppelganger* of a definition that uses the external computation. The doppelganger is a new definition that has the same type as the original definition, but is defined in terms of the trusted proposition. We also make other proof-friendly changes, such as replacing `Float` with `Real`.

In the following command, the attribute `@[abstract_as quadruple]` adds an additional command that introduces a definition that replaces external computations with their facades/abstractions, and makes other proof-friendly changes.
-/
@[abstract_as quadruple]
def timesFour (n : Nat) : Nat := (timesTwo (timesTwo n))

/-!
As we see below, `quadruple` is defined in terms of `double`, which is the facade of `timesTwo`.
-/
/--
info: def quadruple : Nat → Nat :=
fun n => double (double n)
-/
#guard_msgs in
#print quadruple

/-!
## Relative proofs

We can prove properties of the doppelganger using the trusted propositions. In this case, we can prove that `quadruple n = n + n + n + n` for all natural numbers `n` using the trusted proposition that `double n = n + n`.
-/
theorem quad_eqn (n : Nat) : quadruple n = n + n + n + n := by
  grind

/-!
Observe that the proof of `quad_eqn` uses the trusted proposition that `double n = n + n`. Thus, we keep track of trusted propositions. Crucially, these are not introduced as axioms, so there is no danger of introducing inconsistencies into Lean.
-/
/--
info: TrustAndVerify.Examples.quad_eqn [SimplyTrusted (∀ (n : Nat), double n = n + n)] (n : Nat) : quadruple n = n + n + n + n
-/
#guard_msgs in
#check quad_eqn

/-!
## Reference implementation

An alternative to introducing facades and trusting propositions is to introduce a *reference implementation* that is used in proofs. This is a Lean function which we trust to be equivalent to the external computation.
-/
def timesThree (n : Nat) : Nat := fetch
    (encode := fun n => s!"print({n} + {n} + {n})")
    (decode := fun (s : String) => s.toNat!) n

/-- info: 15 -/
#guard_msgs in
#eval timesThree 5

/-!
We give a reference implementation of `timesThree` that is used in proofs. The attribute `@[reference_for timesThree]` maps `timesThree` to `triple` in abstractions.
-/
@[reference_for timesThree, grind .]
def triple (n : Nat) : Nat := n + n + n

/-!
We abstract a function that uses both facades and reference implementations. We see that substitutions are made corresponding to the attributes `@[facade double]` and `@[reference_for timesThree]`.
-/
@[abstract_as sixfold]
def timesSix (n : Nat) : Nat := timesThree (timesTwo n)

/--
info: def sixfold : Nat → Nat :=
fun n => triple (double n)
-/
#guard_msgs in
#print sixfold

theorem sixfold_eqn (n : Nat) : sixfold n = n + n + n + n + n + n := by
  grind

/-!
Note that there is no additional trust needed to prove `sixfold_eqn`, and properties are proved using the reference implementation `triple` and the trusted proposition for `double`.
-/
/--
info: TrustAndVerify.Examples.sixfold_eqn [SimplyTrusted (∀ (n : Nat), double n = n + n)] (n : Nat) :
  sixfold n = n + n + n + n + n + n
-/
#guard_msgs in
#check sixfold_eqn

namespace GPT

noncomputable def sixfold (n : Nat) : Nat :=
  double (triple n)

theorem sixfold_eqn (n : Nat) : sixfold n = 6 * n := by
  grind [sixfold, triple, dble_eqn]

end GPT

namespace gemini

noncomputable def sixfold (n : Nat) : Nat :=
  double (triple n)

theorem sixfold_eq (n : Nat) : sixfold n = 6 * n := by
  unfold sixfold triple
  grind [dble_eqn]

end gemini

end TrustAndVerify.Examples
