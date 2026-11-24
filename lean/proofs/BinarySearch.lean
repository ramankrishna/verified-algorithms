import Mathlib

namespace VerifiedAlgorithms

/-- Binary search for the least index in [lo, hi) where a monotone predicate holds
(returns hi if there is none). This is `bisect_left` in Python. -/
def lowerBound (p : ℕ → Bool) (lo hi : ℕ) : ℕ :=
  if h : lo < hi then
    if p ((lo + hi) / 2) then lowerBound p lo ((lo + hi) / 2)
    else lowerBound p ((lo + hi) / 2 + 1) hi
  else lo
termination_by hi - lo
decreasing_by all_goals omega

theorem lowerBound_spec_aux (p : ℕ → Bool) (hp : ∀ i j, i ≤ j → p i = true → p j = true)
    (lo hi : ℕ) (hle : lo ≤ hi) :
    lo ≤ lowerBound p lo hi ∧ lowerBound p lo hi ≤ hi ∧
      (∀ i, lo ≤ i → i < lowerBound p lo hi → p i = false) ∧
      (∀ i, lowerBound p lo hi ≤ i → i < hi → p i = true) := by
  rw [lowerBound]
  split_ifs with h hm
  · obtain ⟨h1, h2, h3, h4⟩ := lowerBound_spec_aux p hp lo ((lo + hi) / 2) (by omega)
    refine ⟨h1, by omega, h3, ?_⟩
    intro i hi1 hi2
    by_cases him : i < (lo + hi) / 2
    · exact h4 i hi1 him
    · exact hp _ _ (by omega) hm
  · obtain ⟨h1, h2, h3, h4⟩ := lowerBound_spec_aux p hp ((lo + hi) / 2 + 1) hi (by omega)
    refine ⟨by omega, h2, ?_, h4⟩
    intro i hi1 hi2
    by_cases him : i ≤ (lo + hi) / 2
    · cases hpi : p i
      · rfl
      · exact absurd (hp _ _ him hpi) hm
    · exact h3 i (by omega) hi2
  · refine ⟨le_refl _, hle, fun i h1 h2 => absurd h2 (by omega),
      fun i h1 h2 => absurd h2 (by omega)⟩
termination_by hi - lo

/-- For a monotone predicate, binary search returns the boundary: p is false
on [lo, r) and true on [r, hi). -/
theorem lowerBound_spec (p : ℕ → Bool) (hp : ∀ i j, i ≤ j → p i = true → p j = true)
    (lo hi : ℕ) (hle : lo ≤ hi) :
    lo ≤ lowerBound p lo hi ∧ lowerBound p lo hi ≤ hi ∧
      (∀ i, lo ≤ i → i < lowerBound p lo hi → p i = false) ∧
      (∀ i, lowerBound p lo hi ≤ i → i < hi → p i = true) := by
  exact lowerBound_spec_aux p hp lo hi hle

end VerifiedAlgorithms
