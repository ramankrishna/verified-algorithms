import FormalConjecturesUtil

namespace VerifiedAlgorithms

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

theorem dist_succ_le_tree (G : SimpleGraph α) (h : G.Connected) (u v : α) :
    G.dist u v + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist u v
  have hpath : p.IsPath := p.isPath_of_length_eq_dist hp
  have hT := Walk.induce_support_isTree_of_length_eq_dist p hp
  have hcard : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hpath.support_nodup, Walk.length_support]
  have := card_le_largestInducedTreeSize hT
  omega

/-- BFS radius bound: a shortest path between two vertices induces a path (hence a tree),
so every connected graph has an induced tree on at least rad(G) + 1 vertices. -/
theorem radius_succ_le_tree (G : SimpleGraph α) (h : G.Connected) :
    G.radius.toNat + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_radius_of_finite
  have : G.radius.toNat = G.dist u v := by
    rw [← huv]
    rfl
  rw [this]
  exact dist_succ_le_tree G h u v

end VerifiedAlgorithms
