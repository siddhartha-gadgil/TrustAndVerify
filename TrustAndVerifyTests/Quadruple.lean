import TrustAndVerify

namespace TrustAndVerify.Examples

#pipe_python

@[facade double]
def timesTwo (n : Nat) : Nat :=
    fetch (encode := fun n => s!"print({n})") (decode := fun (s : String) => s.toNat!) n

/-- info: opaque double : Nat → Nat -/
#guard_msgs in
#print double

trust ∀ n, double n = n + n

/-- info: #[(trusted_17294129397862412764, ∀ n, double n = n + n)] -/
#guard_msgs in
#eval TrustState.viewTrusts

@[abstract_as quadruple]
def timesFour (n : Nat) : Nat := (timesTwo (timesTwo n))

/--
info: def quadruple : Nat → Nat :=
fun n => double (double n)
-/
#guard_msgs in
#print quadruple

example (n : Nat) : quadruple n = n + n + n + n := by
  grind

#pipe_python

def timesThree (n : Nat) : Nat := fetch
    (encode := fun n => s!"print({n} + {n} + {n})")
    (decode := fun (s : String) => s.toNat!) n

/-- info: 15 -/
#guard_msgs in
#eval timesThree 5


@[reference_for timesThree, grind .]
def triple (n : Nat) : Nat := n + n + n

@[abstract_as sixfold]
def timesSix (n : Nat) : Nat := timesThree (timesTwo n)

/--
info: def sixfold : Nat → Nat :=
fun n => triple (double n)
-/
#guard_msgs in
#print sixfold

example (n : Nat) : sixfold n = n + n + n + n + n + n := by
  grind

end TrustAndVerify.Examples
