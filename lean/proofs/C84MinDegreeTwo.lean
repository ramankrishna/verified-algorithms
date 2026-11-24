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

theorem radius_succ_le_tree_aux (G : SimpleGraph α) (h : G.Connected) :
    G.radius.toNat + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_radius_of_finite
  have : G.radius.toNat = G.dist u v := by
    rw [← huv]
    rfl
  rw [this]
  exact dist_succ_le_tree G h u v

/-- WOWII 84 when the minimum degree is at least 2: tree(G) ≥ 2·rad(G)/δ(G). -/
theorem c84_of_two_le_minDegree (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) (hδ : 2 ≤ G.minDegree) :
    2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ (largestInducedTreeSize G : ℝ) := by
  have hr := radius_succ_le_tree_aux G h
  have h2R : (2 : ℝ) ≤ G.minDegree := by exact_mod_cast hδ
  have hδR : (0 : ℝ) < G.minDegree := by linarith
  rw [div_le_iff₀ hδR]
  have hrR : (G.radius.toNat : ℝ) + 1 ≤ largestInducedTreeSize G := by exact_mod_cast hr
  have h0 : (0 : ℝ) ≤ G.radius.toNat := by positivity
  nlinarith

end VerifiedAlgorithms
