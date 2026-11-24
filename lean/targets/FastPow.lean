import Mathlib

namespace VerifiedAlgorithms

/-- Exponentiation by squaring: O(log e) multiplications. -/
def powFast (b : ℕ) (e : ℕ) : ℕ :=
  if h : e = 0 then 1
  else
    let half := powFast b (e / 2)
    if e % 2 = 0 then half * half else half * half * b
termination_by e
decreasing_by omega

/-- Exponentiation by squaring computes b ^ e. -/
theorem powFast_eq (b e : ℕ) : powFast b e = b ^ e := by
  sorry

end VerifiedAlgorithms
