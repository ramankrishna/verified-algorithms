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

/-- For a monotone predicate, binary search returns the boundary: p is false
on [lo, r) and true on [r, hi). -/
theorem lowerBound_spec (p : ℕ → Bool) (hp : ∀ i j, i ≤ j → p i = true → p j = true)
    (lo hi : ℕ) (hle : lo ≤ hi) :
    lo ≤ lowerBound p lo hi ∧ lowerBound p lo hi ≤ hi ∧
      (∀ i, lo ≤ i → i < lowerBound p lo hi → p i = false) ∧
      (∀ i, lowerBound p lo hi ≤ i → i < hi → p i = true) := by
  sorry

end VerifiedAlgorithms
