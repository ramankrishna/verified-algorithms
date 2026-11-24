import Mathlib

namespace VerifiedAlgorithms

/-- Euclid's algorithm: gcd(a, b) = gcd(b, a mod b), gcd(a, 0) = a. -/
def euclid (a b : ℕ) : ℕ :=
  if h : b = 0 then a else euclid b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- Euclid's algorithm computes the greatest common divisor. -/
theorem euclid_eq_gcd (a b : ℕ) : euclid a b = Nat.gcd a b := by
  sorry

end VerifiedAlgorithms
