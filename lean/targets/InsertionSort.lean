import Mathlib

namespace VerifiedAlgorithms

/-- Insert x into a sorted list. -/
def insertSorted (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

/-- Insertion sort. -/
def insSort : List ℕ → List ℕ
  | [] => []
  | x :: xs => insertSorted x (insSort xs)

/-- Insertion sort returns a sorted permutation of its input. -/
theorem insSort_correct (l : List ℕ) :
    List.Pairwise (· ≤ ·) (insSort l) ∧ List.Perm (insSort l) l := by
  sorry

end VerifiedAlgorithms
