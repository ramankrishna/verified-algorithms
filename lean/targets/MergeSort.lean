import Mathlib

namespace VerifiedAlgorithms

/-- Merge two lists, taking the smaller head first. -/
def merge : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys

/-- Top-down merge sort: split in half, sort each half, merge. -/
def mergeSort (l : List ℕ) : List ℕ :=
  if h : l.length < 2 then l
  else merge (mergeSort (l.take (l.length / 2))) (mergeSort (l.drop (l.length / 2)))
termination_by l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]
  all_goals omega

/-- Merge sort returns a sorted permutation of its input. -/
theorem mergeSort_correct (l : List ℕ) :
    List.Pairwise (· ≤ ·) (mergeSort l) ∧ List.Perm (mergeSort l) l := by
  sorry

end VerifiedAlgorithms
