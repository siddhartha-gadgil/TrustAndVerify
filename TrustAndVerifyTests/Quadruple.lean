import TrustAndVerify

namespace TrustAndVerify.Examples

@[facade double]
def timesTwo (n : Nat) : Nat := n + n

trust ∀ n, double n = n + n

@[abstract quadruple]
def timesFour (n : Nat) : Nat := (timesTwo (timesTwo n))

/--
info: def quadruple : Nat → Nat :=
fun n => double (double n)
-/
#guard_msgs in
#print quadruple

example (n : Nat) : quadruple n = n + n + n + n := by
  grind

end TrustAndVerify.Examples
