import FormalConjecturesUtil

namespace VerifiedAlgorithms

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- BFS radius bound: a shortest path between two vertices induces a path (hence a tree),
so every connected graph has an induced tree on at least rad(G) + 1 vertices. -/
theorem radius_succ_le_tree (G : SimpleGraph α) (h : G.Connected) :
    G.radius.toNat + 1 ≤ largestInducedTreeSize G := by
  sorry

end VerifiedAlgorithms
