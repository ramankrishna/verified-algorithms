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

theorem perm_insertSorted (x : ℕ) (l : List ℕ) : List.Perm (insertSorted x l) (x :: l) := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    simp only [insertSorted]
    split_ifs
    · exact List.Perm.refl _
    · exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

theorem pairwise_insertSorted (x : ℕ) (l : List ℕ) (h : List.Pairwise (· ≤ ·) l) :
    List.Pairwise (· ≤ ·) (insertSorted x l) := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    rw [List.pairwise_cons] at h
    simp only [insertSorted]
    split_ifs with hxy
    · rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.mpr h⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hxy
      · exact le_trans hxy (h.1 z hz)
    · rw [List.pairwise_cons]
      refine ⟨?_, ih h.2⟩
      intro z hz
      have hz' := (perm_insertSorted x ys).subset hz
      rcases List.mem_cons.mp hz' with rfl | hz'
      · omega
      · exact h.1 z hz'

/-- Insertion sort returns a sorted permutation of its input. -/
theorem insSort_correct (l : List ℕ) :
    List.Pairwise (· ≤ ·) (insSort l) ∧ List.Perm (insSort l) l := by
  induction l with
  | nil => simp [insSort]
  | cons x xs ih =>
    simp only [insSort]
    exact ⟨pairwise_insertSorted x _ ih.1,
      (perm_insertSorted x _).trans (List.Perm.cons x ih.2)⟩

end VerifiedAlgorithms
