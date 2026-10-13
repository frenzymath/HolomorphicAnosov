import HolomorphicAnosov.Topology.GallierXuTwoVertexSupport

noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu

/-- A standard simplex point supported at one vertex is that vertex's singleton coordinate. This is the vertex case in the Lee quotient comparison. -/
lemma simplex_single_vertex_support {N : ℕ} {x : Fin N → ℝ}
    (hx : x ∈ {f : Fin N → ℝ | (∀ v, 0 ≤ f v) ∧ ∑ v, f v = 1}) {u : Fin N}
    (hz : ∀ w, w ≠ u → x w = 0) : x = Pi.single u 1 := by
  funext w
  by_cases h : w = u
  · subst w
    have hs : x u = 1 := by
      rw [← hx.2]
      symm
      apply Finset.sum_eq_single u
      · intro b hb hbu
        exact hz b hbu
      · simp
    simp [hs]
  · simp [hz w h, h]

end HolomorphicAnosov.Topology.GallierXu
