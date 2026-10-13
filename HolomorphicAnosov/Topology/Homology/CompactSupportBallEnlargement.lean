import Mathlib.Topology.MetricSpace.Thickening

/-!
# Finite closed-ball enlargements avoiding a boundary support

Source: Hatcher, Algebraic Topology, Lemma 3.27, step (4), pp.237–238.
This is the geometric enlargement of a compact support away from the finite
boundary-image support of a relative cycle. No homology vanishing is assumed.
-/

open Set Metric

namespace HolomorphicAnosov

/-- Hatcher Lemma 3.27, step (4): enlarge a compact support to finitely many
closed balls centered in it, while avoiding a prescribed disjoint closed set.
The balls share a positive radius below any requested positive bound.

Proof: the complement of the closed set is an open neighborhood of the compact
support, so it contains a positive closed thickening. Choose a smaller positive
radius, also smaller than the prescribed bound. The open balls of this radius
centered on the support cover it; compactness selects finitely many. Their
closed balls lie in the chosen thickening, hence avoid the closed set. They
are compact in a proper metric space. Their open interiors cover the original
support, so it lies in the interior of their finite union. Empty support and
empty excluded set require no separate positive-distance convention. -/
theorem compact_support_ball_enlargement
    {E : Type*} [MetricSpace E] [ProperSpace E]
    (K C : Set E) (hK : IsCompact K) (hC : IsClosed C) (hKC : Disjoint K C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ ∃ centers : Finset K,
      K ⊆ interior (⋃ x ∈ centers, closedBall (x : E) r) ∧
      IsCompact (⋃ x ∈ centers, closedBall (x : E) r) ∧
      Disjoint (⋃ x ∈ centers, closedBall (x : E) r) C := by
  classical
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_cthickening_subset_open hC.isOpen_compl
    hKC.subset_compl_right
  let r := min δ ε / 2
  have hr : 0 < r := half_pos (lt_min hδ hε)
  have hrδ : r ≤ δ := (half_le_self (le_of_lt (lt_min hδ hε))).trans (min_le_left _ _)
  have hrε : r < ε := (half_lt_self (lt_min hδ hε)).trans_le (min_le_right _ _)
  have hcover : K ⊆ ⋃ x : K, ball (x : E) r := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self hr⟩
  obtain ⟨centers, hcenters⟩ := hK.elim_finite_subcover
    (fun x : K ↦ ball (x : E) r) (fun _ ↦ isOpen_ball) hcover
  refine ⟨r, hr, hrε, centers, ?_, ?_, ?_⟩
  · apply hcenters.trans
    apply (isOpen_biUnion fun _ _ ↦ isOpen_ball).subset_interior_iff.mpr
    exact iUnion₂_mono fun _ _ ↦ ball_subset_closedBall
  · exact centers.isCompact_biUnion fun x hx ↦ isCompact_closedBall (x : E) r
  · apply disjoint_left.mpr
    intro y hy hyC
    obtain ⟨x, hx, hyball⟩ := mem_iUnion₂.mp hy
    exact hthick ((closedBall_subset_cthickening x.property δ)
      (closedBall_subset_closedBall hrδ hyball)) hyC

end HolomorphicAnosov
