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

theorem perm_merge : ∀ (xs ys : List ℕ), List.Perm (merge xs ys) (xs ++ ys)
  | [], ys => by simp [merge]
  | x :: xs, [] => by simp [merge]
  | x :: xs, y :: ys => by
    simp only [merge]
    split_ifs
    · exact (perm_merge xs (y :: ys)).cons x
    · exact ((perm_merge (x :: xs) ys).cons y).trans List.perm_middle.symm
termination_by xs ys => xs.length + ys.length

theorem pairwise_merge : ∀ (xs ys : List ℕ), List.Pairwise (· ≤ ·) xs →
    List.Pairwise (· ≤ ·) ys → List.Pairwise (· ≤ ·) (merge xs ys)
  | [], ys, _, hy => by simpa [merge] using hy
  | x :: xs, [], hx, _ => by simpa [merge] using hx
  | x :: xs, y :: ys, hx, hy => by
    have hx' := List.pairwise_cons.mp hx
    have hy' := List.pairwise_cons.mp hy
    simp only [merge]
    split_ifs with hxy
    · refine List.pairwise_cons.mpr ⟨?_, pairwise_merge xs (y :: ys) hx'.2 hy⟩
      intro z hz
      rcases List.mem_append.mp ((perm_merge xs (y :: ys)).subset hz) with hz | hz
      · exact hx'.1 z hz
      · rcases List.mem_cons.mp hz with rfl | hz
        · exact hxy
        · exact le_trans hxy (hy'.1 z hz)
    · refine List.pairwise_cons.mpr ⟨?_, pairwise_merge (x :: xs) ys hx hy'.2⟩
      intro z hz
      rcases List.mem_append.mp ((perm_merge (x :: xs) ys).subset hz) with hz | hz
      · rcases List.mem_cons.mp hz with rfl | hz
        · omega
        · exact le_trans (by omega : y ≤ x) (hx'.1 z hz)
      · exact hy'.1 z hz
termination_by xs ys _ _ => xs.length + ys.length

theorem mergeSort_correct_aux (l : List ℕ) :
    List.Pairwise (· ≤ ·) (mergeSort l) ∧ List.Perm (mergeSort l) l := by
  rw [mergeSort]
  split_ifs with h
  · refine ⟨?_, List.Perm.refl _⟩
    rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp
    · simp
    · simp at h
  · have h1 := mergeSort_correct_aux (l.take (l.length / 2))
    have h2 := mergeSort_correct_aux (l.drop (l.length / 2))
    refine ⟨pairwise_merge _ _ h1.1 h2.1, (perm_merge _ _).trans ?_⟩
    have h3 := h1.2.append h2.2
    rwa [List.take_append_drop] at h3
termination_by l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]
  all_goals omega

/-- Merge sort returns a sorted permutation of its input. -/
theorem mergeSort_correct (l : List ℕ) :
    List.Pairwise (· ≤ ·) (mergeSort l) ∧ List.Perm (mergeSort l) l := by
  exact mergeSort_correct_aux l

end VerifiedAlgorithms
