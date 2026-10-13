import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.GaugeRescale

namespace HolomorphicAnosov

/-- The Euclidean coordinate space and the sup-norm coordinate space admit
a homeomorphism preserving the value of the norm. Source: Bredon,
Topology and Geometry I.16, pp.56–57, radial comparison of convex bodies,
as used to change characteristic disks in Hatcher's cell attachments.

Proof: pull the sup-norm unit ball back through the linear coordinate
homeomorphism. It and the Euclidean unit ball are convex bounded
neighborhoods of zero. Gauge rescaling maps one body radially to the
other, and its gauge identity states that the sup norm of the new
coordinates equals the Euclidean norm of the old ones. This works in
zero dimension without a nonzero-direction choice. -/
theorem euclidean_sup_radial_homeomorph (k : ℕ) :
    ∃ e : EuclideanSpace ℝ (Fin k) ≃ₜ (Fin k → ℝ), ∀ x, ‖e x‖ = ‖x‖ := by
  let E := EuclideanSpace ℝ (Fin k)
  let F := Fin k → ℝ
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k ↦ ℝ)
  let S : Set E := Metric.closedBall 0 1
  let T : Set E := L ⁻¹' Metric.closedBall 0 1
  have hSc : Convex ℝ S := convex_closedBall _ _
  have hS₀ : S ∈ nhds 0 := Metric.closedBall_mem_nhds _ zero_lt_one
  have hSb : Bornology.IsVonNBounded ℝ S := NormedSpace.isVonNBounded_closedBall _ _ _
  have hTc : Convex ℝ T := (convex_closedBall (0 : F) 1).linear_preimage L.toLinearMap
  have hT₀ : T ∈ nhds 0 := L.continuous.continuousAt.preimage_mem_nhds
    (by simpa using Metric.closedBall_mem_nhds (0 : F) zero_lt_one)
  have hTb : Bornology.IsVonNBounded ℝ T := by
    have h := (NormedSpace.isVonNBounded_closedBall ℝ F 1).image L.symm.toContinuousLinearMap
    apply h.subset
    intro x hx
    exact ⟨L x, hx, L.symm_apply_apply x⟩
  have hSg (x : E) : gauge S x = ‖x‖ := by
    rw [show S = Metric.closedBall (0 : E) 1 by rfl,
      gauge_closedBall zero_le_one, div_one]
  have hTg (x : E) : gauge T x = ‖L x‖ := by
    have h : gauge T x = gauge (Metric.closedBall (0 : F) 1) (L x) := by
      simp only [gauge_def']
      congr 1
    rw [h, gauge_closedBall zero_le_one, div_one]
  let H := gaugeRescaleHomeomorph S T hSc hS₀ hSb hTc hT₀ hTb
  refine ⟨H.trans L.toHomeomorph, ?_⟩
  intro x
  have hg := gauge_gaugeRescale S (absorbent_nhds_zero hT₀) hTb x
  change gauge T (H x) = gauge S x at hg
  rw [hTg, hSg] at hg
  exact hg

end HolomorphicAnosov
