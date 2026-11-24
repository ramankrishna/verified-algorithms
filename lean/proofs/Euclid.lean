import Mathlib

namespace VerifiedAlgorithms

/-- Euclid's algorithm: gcd(a, b) = gcd(b, a mod b), gcd(a, 0) = a. -/
def euclid (a b : ℕ) : ℕ :=
  if h : b = 0 then a else euclid b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

theorem euclid_eq_gcd_aux : ∀ (b a : ℕ), euclid a b = Nat.gcd a b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a
    rw [euclid]
    by_cases hb : b = 0
    · subst hb
      simp
    · rw [dif_neg hb, ih (a % b) (Nat.mod_lt _ (Nat.pos_of_ne_zero hb)) b,
        Nat.gcd_comm a b, Nat.gcd_rec b a, Nat.gcd_comm]

/-- Euclid's algorithm computes the greatest common divisor. -/
theorem euclid_eq_gcd (a b : ℕ) : euclid a b = Nat.gcd a b := by
  exact euclid_eq_gcd_aux b a

end VerifiedAlgorithms
