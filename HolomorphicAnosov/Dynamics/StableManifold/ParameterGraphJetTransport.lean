import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.NormCore
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.EventuallySlopeBound
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open Filter _root_.Topology
namespace HolomorphicAnosov
open BoundedLipschitzJets

/-- HPS, *Invariant Manifolds*, pp.33–34 and pp.57–58: transport a local
representative comparison to the jet norm. Suppose the centered return R is
continuous at zero, with eventual slope at most c. If the output difference
is eventually bounded by b times the input difference evaluated at R, then
the output jet norm is at most bc times the input jet norm.

For every η larger than the input slope, the input norm is eventually at
most η times the argument norm. Its value at zero is zero, so this estimate
extends from the punctured filter to the full neighborhood. Pull it back
by R and combine the two supplied bounds. The resulting bcη is an eventual
output slope bound. Let η decrease to the input slope. This explicitly
covers a return which is zero at nonzero displacements; no injectivity or
punctured-filter mapping assumption is made. Zero-dimensional fibres and
zero b or c are also included. -/
theorem parameter_graph_jet_transport
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : BoundedRepresentative X Y) (P : BoundedRepresentative U V)
    (R : X → U) (hR : ContinuousAt R 0) (hR0 : R 0 = 0)
    (b c : NNReal)
    (hbound : ∀ᶠ x in 𝓝 (0 : X), ‖R x‖ ≤ (c : ℝ) * ‖x‖)
    (hcompare : ∀ᶠ x in 𝓝 (0 : X),
      ‖(Q : X → Y) x‖ ≤ (b : ℝ) * ‖(P : U → V) (R x)‖) :
    ‖jetClass X Y Q‖ ≤ (b : ℝ) * c * ‖jetClass U V P‖ := by
  have hη : ∀ η : ℝ, ‖jetClass U V P‖ < η →
      ‖jetClass X Y Q‖ ≤ (b : ℝ) * c * η := by
    intro η hη
    have hη0 : 0 ≤ η := (norm_nonneg _).trans hη.le
    have hin : ∀ᶠ u in 𝓝 (0 : U), ‖(P : U → V) u‖ ≤ η * ‖u‖ := by
      rw [← nhdsNE_sup_pure (0 : U), Filter.eventually_sup]
      refine ⟨eventually_slope_le U V P hη, ?_⟩
      simpa only [Filter.eventually_pure, P.property.1, norm_zero, mul_zero]
        using (le_refl (0 : ℝ))
    have hout : (b : ℝ) * c * η ∈ slopeBounds X Y Q := by
      refine ⟨mul_nonneg (mul_nonneg b.2 c.2) hη0, ?_⟩
      have hinR := (show Tendsto R (𝓝 0) (𝓝 0) by
        simpa only [hR0] using hR.tendsto).eventually hin
      filter_upwards [hcompare.filter_mono nhdsWithin_le_nhds,
        hbound.filter_mono nhdsWithin_le_nhds, hinR.filter_mono nhdsWithin_le_nhds]
        with x hx hxR hxP
      calc
        ‖(Q : X → Y) x‖ ≤ (b : ℝ) * ‖(P : U → V) (R x)‖ := hx
        _ ≤ (b : ℝ) * (η * ‖R x‖) := mul_le_mul_of_nonneg_left hxP b.2
        _ ≤ (b : ℝ) * (η * ((c : ℝ) * ‖x‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxR hη0) b.2
        _ = ((b : ℝ) * c * η) * ‖x‖ := by ring
    change sInf (slopeBounds X Y Q) ≤ _
    exact csInf_le ⟨0, fun _ h ↦ h.1⟩ hout
  have hlim : Tendsto (fun η : ℝ ↦ (b : ℝ) * c * η)
      (𝓝[>] ‖jetClass U V P‖) (𝓝 ((b : ℝ) * c * ‖jetClass U V P‖)) :=
    (continuous_const.mul continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with η hη'
  exact hη η hη'

end HolomorphicAnosov
