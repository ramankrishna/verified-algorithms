import FormalConjecturesUtil

namespace VerifiedAlgorithms

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- WOWII 84 when the minimum degree is at least 2: tree(G) ≥ 2·rad(G)/δ(G). -/
theorem c84_of_two_le_minDegree (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) (hδ : 2 ≤ G.minDegree) :
    2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ (largestInducedTreeSize G : ℝ) := by
  sorry

end VerifiedAlgorithms
