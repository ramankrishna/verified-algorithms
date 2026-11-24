import Mathlib

namespace VerifiedAlgorithms

/-- Directed graph on `Fin n` with non-negative integer weights; `none` means no edge. -/
abbrev Weights (n : ℕ) := Fin n → Fin n → Option ℕ

/-- Minimum where `none` means infinity. -/
def omin : Option ℕ → Option ℕ → Option ℕ
  | none, b => b
  | some a, none => some a
  | some a, some b => some (min a b)

/-- Relax every edge leaving `u`, whose settled distance is `du`. -/
def relax {n : ℕ} (w : Weights n) (dist : Fin n → Option ℕ) (u : Fin n) (du : ℕ) :
    Fin n → Option ℕ :=
  fun v => match w u v with
    | none => dist v
    | some c => omin (dist v) (some (du + c))

/-- The unvisited vertex with the smallest finite tentative distance (linear scan). -/
def pickMin {n : ℕ} (dist : Fin n → Option ℕ) (visited : Finset (Fin n)) :
    Option (Fin n × ℕ) :=
  (List.finRange n).foldl (fun best v =>
    if v ∈ visited then best else
    match dist v, best with
    | none, _ => best
    | some d, none => some (v, d)
    | some d, some (b, db) => if d < db then some (v, d) else some (b, db)) none

/-- Main loop: settle the closest unvisited vertex, relax its edges, repeat (fuel = n). -/
def dijkstraLoop {n : ℕ} (w : Weights n) :
    ℕ → (Fin n → Option ℕ) → Finset (Fin n) → (Fin n → Option ℕ)
  | 0, dist, _ => dist
  | k + 1, dist, visited =>
    match pickMin dist visited with
    | none => dist
    | some (u, du) => dijkstraLoop w k (relax w dist u du) (insert u visited)

/-- Dijkstra's algorithm from source `s` (array version, O(n²)). -/
def dijkstra {n : ℕ} (w : Weights n) (s : Fin n) : Fin n → Option ℕ :=
  dijkstraLoop w n (fun v => if v = s then some 0 else none) ∅

/-- `Reach w s v c`: some walk from `s` to `v` has total weight `c`. -/
inductive Reach {n : ℕ} (w : Weights n) (s : Fin n) : Fin n → ℕ → Prop
  | refl : Reach w s s 0
  | step {u v : Fin n} {c c' : ℕ} : Reach w s u c → w u v = some c' → Reach w s v (c + c')

/-- Dijkstra is correct: every reported distance is the weight of a real walk, and it is
at most the weight of every walk. So it is exactly the shortest-path distance, and `none`
exactly when `v` is unreachable. -/
theorem dijkstra_correct {n : ℕ} (w : Weights n) (s v : Fin n) :
    (∀ c, dijkstra w s v = some c → Reach w s v c) ∧
    (∀ c, Reach w s v c → ∃ c₀, dijkstra w s v = some c₀ ∧ c₀ ≤ c) := by
  sorry

end VerifiedAlgorithms
