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

theorem powFast_eq_aux (b : ℕ) : ∀ e, powFast b e = b ^ e := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rw [powFast]
    by_cases he : e = 0
    · subst he
      simp
    · rw [dif_neg he]
      have hk := ih (e / 2) (by omega)
      simp only [hk]
      split_ifs with h2
      · rw [← pow_add]
        congr 1
        omega
      · rw [← pow_add, ← pow_succ]
        congr 1
        omega

/-- Exponentiation by squaring computes b ^ e. -/
theorem powFast_eq (b e : ℕ) : powFast b e = b ^ e := by
  exact powFast_eq_aux b e

end VerifiedAlgorithms
