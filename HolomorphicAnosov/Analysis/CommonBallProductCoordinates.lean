import HolomorphicAnosov.Analysis.CommonBallInverse
import Mathlib.Topology.Homeomorph.Defs

open Set
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/-- The common-ball inverse gives actual product coordinates on the open inverse
image of its target ball. This agent-written topological identification expands
the closed-ball application of Fisher–Hasselblatt, *Hyperbolic flows*, Proposition 12.1.3(1),(2),
pp.578–579. The contraction theorem supplies a continuous solution in the half
ball. Send `(p,w)` to `(H p w,p)` and send `(z,p)` to the supplied solution.
Uniqueness on the closed ball and the solution equation give both inverse laws.
Continuity on the closed ball suffices for the forward map on the open source;
the source is open by the continuous preimage theorem on the open ball.
Empty parameter spaces and the zero normed group are permitted. -/
theorem common_ball_product_coordinates
    {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E] [CompleteSpace E]
    (H : P → E → E) (r : ℝ) (hr : 0 < r)
    (hc : ContinuousOn (fun x : P × E ↦ H x.1 x.2)
      (Set.univ ×ˢ Metric.closedBall (0 : E) r))
    (hcenter : ∀ p, ‖H p 0‖ < r / 8)
    (happrox : ∀ p, ∀ v ∈ Metric.closedBall (0 : E) r,
      ∀ w ∈ Metric.closedBall (0 : E) r,
      ‖H p v - H p w - (v - w)‖ ≤ (1 / 2 : ℝ) * ‖v - w‖) :
    let U : Set (P × E) := {x | x.2 ∈ Metric.ball (0 : E) r ∧
      H x.1 x.2 ∈ Metric.ball (0 : E) (r / 8)}
    IsOpen U ∧ ∃ c : U ≃ₜ (Metric.ball (0 : E) (r / 8) × P),
      ∀ x : U, ((c x).1 : E) = H x.1.1 x.1.2 ∧ (c x).2 = x.1.1 := by
  classical
  let U : Set (P × E) := {x | x.2 ∈ Metric.ball (0 : E) r ∧
    H x.1 x.2 ∈ Metric.ball (0 : E) (r / 8)}
  have hcf (v : E) (hv : v ∈ Metric.closedBall (0 : E) r) :
      Continuous (fun p ↦ H p v) := by
    exact hc.comp_continuous (continuous_id.prodMk continuous_const) (fun p ↦ ⟨trivial, hv⟩)
  obtain ⟨v, hvcont, hv⟩ := common_ball_inverse_of_half_identity H r hr hcf hcenter happrox
  have hopen : IsOpen U := by
    have he : U = (Set.univ ×ˢ Metric.ball (0 : E) r) ∩
        (fun x : P × E ↦ H x.1 x.2) ⁻¹' Metric.ball (0 : E) (r / 8) := by
      ext x
      simp only [U, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod,
        Set.mem_univ, true_and, Set.mem_preimage]
    rw [he]
    exact (hc.mono (fun x hx ↦ ⟨hx.1, Metric.ball_subset_closedBall hx.2⟩)).isOpen_inter_preimage
      (isOpen_univ.prod Metric.isOpen_ball) Metric.isOpen_ball
  let f : U → Metric.ball (0 : E) (r / 8) × P :=
    fun x ↦ (⟨H x.1.1 x.1.2, x.2.2⟩, x.1.1)
  let g : Metric.ball (0 : E) (r / 8) × P → U := fun z ↦
    ⟨(z.2, v (z.2, z.1)), by
      refine ⟨?_, ?_⟩
      · simpa only [Metric.mem_ball, dist_zero_right] using
          lt_trans (hv (z.2, z.1)).1 (by linarith : r / 2 < r)
      · rw [(hv (z.2, z.1)).2.1]
        exact z.1.2⟩
  have hleft (x : U) : g (f x) = x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    exact ((hv (x.1.1, (f x).1)).2.2 x.1.2
      (Metric.ball_subset_closedBall x.2.1) rfl).symm
  have hright (z : Metric.ball (0 : E) (r / 8) × P) : f (g z) = z := by
    apply Prod.ext
    · exact Subtype.ext (hv (z.2, z.1)).2.1
    · rfl
  have hfc : Continuous f := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact hc.comp_continuous continuous_subtype_val
        (fun x ↦ ⟨trivial, Metric.ball_subset_closedBall x.2.1⟩)
    · exact continuous_fst.comp continuous_subtype_val
  have hgc : Continuous g := by
    apply Continuous.subtype_mk
    exact continuous_snd.prodMk (hvcont.comp (continuous_snd.prodMk continuous_fst))
  exact ⟨hopen, ⟨⟨f, g, hleft, hright⟩, hfc, hgc⟩, fun x ↦ ⟨rfl, rfl⟩⟩

end HolomorphicAnosov.Analysis
