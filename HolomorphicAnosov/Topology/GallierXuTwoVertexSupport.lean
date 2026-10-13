import HolomorphicAnosov.Topology.GallierXuOriginalEdgeParameter

noncomputable section
open Set Topology _root_.Topology
open scoped BigOperators
namespace HolomorphicAnosov.Topology.GallierXu

/-- A point of the standard simplex supported on two distinct ordered vertices
is their native normalized edge point. Source: the barycentric edge-fibre
calculation in Lee Proposition 6.14, p.173. Restrict the sum-one equation to
the two vertices; the upper vertex coefficient is in [0,1], and all remaining
coordinates vanish. -/
lemma simplex_two_vertex_support {N : ℕ} {x : Fin N → ℝ}
    (hx : x ∈ {f : Fin N → ℝ | (∀ v, 0 ≤ f v) ∧ ∑ v, f v = 1}) {u v : Fin N} (huv : u < v)
    (hz : ∀ w, w ∉ ({u, v} : Finset (Fin N)) → x w = 0) :
    x v ∈ Icc (0 : ℝ) 1 ∧ x = originalEdgePoint u v (x v) := by
  have hne : u ≠ v := ne_of_lt huv
  have hsum : x u + x v = 1 := by
    have hs : ∑ w ∈ ({u, v} : Finset (Fin N)), x w = 1 := by
      rw [← hx.2]
      apply Finset.sum_subset (by simp)
      intro w hw hnot
      exact hz w hnot
    simpa [Finset.sum_insert, hne] using hs
  refine ⟨⟨hx.1 v, ?_⟩, ?_⟩
  · linarith [hx.1 u]
  · funext w
    by_cases hwu : w = u
    · subst w
      simp [originalEdgePoint, min_eq_left huv.le, max_eq_right huv.le, hne.symm]
      linarith
    · by_cases hwv : w = v
      · subst w
        simp [originalEdgePoint, min_eq_left huv.le, max_eq_right huv.le, hne]
      · have hzero := hz w (by simp [hwu, hwv])
        simp [originalEdgePoint, min_eq_left huv.le, max_eq_right huv.le,
          hwu, hwv, hzero]

/-- The unoriented version of the preceding barycentric calculation uses the
same min/max parameter as OriginalParameters. -/
lemma simplex_two_vertex_support_unordered {N : ℕ} {x : Fin N → ℝ}
    (hx : x ∈ {f : Fin N → ℝ | (∀ v, 0 ≤ f v) ∧ ∑ v, f v = 1}) {u v : Fin N} (huv : u ≠ v)
    (hz : ∀ w, w ∉ ({u, v} : Finset (Fin N)) → x w = 0) :
    ∃ t ∈ Icc (0 : ℝ) 1, x = originalEdgePoint u v t := by
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · obtain ⟨ht, heq⟩ := simplex_two_vertex_support hx hlt hz
    exact ⟨x v, ht, heq⟩
  · have hz' : ∀ w, w ∉ ({v, u} : Finset (Fin N)) → x w = 0 := by
      simpa [Finset.pair_comm] using hz
    obtain ⟨ht, heq⟩ := simplex_two_vertex_support hx hgt hz'
    exact ⟨x u, ht, heq.trans (originalEdgePoint_comm v u (x u))⟩

end HolomorphicAnosov.Topology.GallierXu
