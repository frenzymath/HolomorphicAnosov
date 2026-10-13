import HolomorphicAnosov.Analysis.CommonBallProductCoordinates
import Mathlib.Analysis.Calculus.MeanValue

open Set TopologicalSpace
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/-- Continuous-parameter inverse theorem in normalized coordinates, specializing
Fisher–Hasselblatt, *Hyperbolic flows*, Proposition 12.1.3(1),(2), pp.578–579.
Continuity of the derivative at the base point gives a product neighborhood
where its distance from the identity is at most one half. Choose a closed ball
inside its second factor, then shrink the parameter neighborhood so the center
image has norm less than one eighth of its radius. The convex mean-value theorem
gives the uniform half-identity estimate; the common-ball contraction theorem
then gives the displayed open product coordinates. All source points stay in
the initially prescribed open neighborhood. No parameter derivative is used. -/
theorem parametric_inverse_neighborhood
    {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (f : P → E → E) (δ : P × E → E →L[ℝ] E)
    (S : Set (P × E)) (hS : IsOpen S) (p₀ : P) (hp₀ : (p₀, 0) ∈ S)
    (hf : ContinuousOn (fun x : P × E ↦ f x.1 x.2) S)
    (hδ : ContinuousOn δ S)
    (hd : ∀ x ∈ S, HasFDerivAt (f x.1) (δ x) x.2)
    (hzero : f p₀ 0 = 0) (hid : δ (p₀, 0) = ContinuousLinearMap.id ℝ E) :
    ∃ V : Opens P, ∃ hpV : p₀ ∈ V, ∃ r : ℝ, 0 < r ∧
      let U : Set (V × E) := {x | x.2 ∈ Metric.ball 0 r ∧
        f x.1.1 x.2 ∈ Metric.ball 0 (r / 8)}
      IsOpen U ∧ (⟨p₀, hpV⟩, 0) ∈ U ∧
      (∀ x : U, (x.1.1.1, x.1.2) ∈ S) ∧
      ∃ c : U ≃ₜ (Metric.ball (0 : E) (r / 8) × V),
        ∀ x : U, ((c x).1 : E) = f x.1.1.1 x.1.2 ∧ (c x).2 = x.1.1 := by
  have hbase := hS.mem_nhds hp₀
  have hnear : {x | ‖δ x - ContinuousLinearMap.id ℝ E‖ < (1 / 2 : ℝ)} ∈
      𝓝 (p₀, 0) := by
    exact ((hδ.continuousAt hbase).sub_const (ContinuousLinearMap.id ℝ E)).norm.eventually
      (gt_mem_nhds (by simp [hid]))
  obtain ⟨V₀, hV₀, W₀, hW₀, hprod⟩ := mem_nhds_prod_iff.mp (Filter.inter_mem hbase hnear)
  obtain ⟨V₁, hV₁sub, hV₁open, hpV₁⟩ := mem_nhds_iff.mp hV₀
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hW₀
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hball (w : E) (hw : w ∈ Metric.closedBall (0 : E) r) : w ∈ W₀ := by
    apply hεsub
    exact (Metric.closedBall_subset_ball (by dsimp [r]; linarith)) hw
  have hcenter : {p | ‖f p 0‖ < r / 8} ∈ 𝓝 p₀ := by
    have hc : ContinuousAt (fun p ↦ f p 0) p₀ :=
      (hf.continuousAt hbase).comp (f := fun p : P ↦ (p, (0 : E)))
        (continuousAt_id.prodMk continuousAt_const)
    exact hc.norm.eventually (gt_mem_nhds (by simpa only [hzero, norm_zero] using (by positivity : (0 : ℝ) < r / 8)))
  obtain ⟨V₂, hV₂sub, hV₂open, hpV₂⟩ := mem_nhds_iff.mp hcenter
  let V : Opens P := ⟨V₁ ∩ V₂, hV₁open.inter hV₂open⟩
  have hpV : p₀ ∈ V := ⟨hpV₁, hpV₂⟩
  have hcontrol (p : V) (w : E) (hw : w ∈ Metric.closedBall (0 : E) r) :
      (p.1, w) ∈ S ∧ ‖δ (p.1, w) - ContinuousLinearMap.id ℝ E‖ < (1 / 2 : ℝ) :=
    hprod ⟨hV₁sub p.2.1, hball w hw⟩
  have hc : ContinuousOn (fun x : V × E ↦ f x.1.1 x.2)
      (univ ×ˢ Metric.closedBall (0 : E) r) := by
    exact hf.comp (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd).continuousOn
      (fun x hx ↦ (hcontrol x.1 x.2 hx.2).1)
  have happ (p : V) (v : E) (hv : v ∈ Metric.closedBall (0 : E) r)
      (w : E) (hw : w ∈ Metric.closedBall (0 : E) r) :
      ‖f p.1 v - f p.1 w - (v - w)‖ ≤ (1 / 2 : ℝ) * ‖v - w‖ := by
    exact (convex_closedBall (0 : E) r).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun x hx ↦ (hd (p.1, x) (hcontrol p x hx).1).hasFDerivWithinAt)
      (fun x hx ↦ (hcontrol p x hx).2.le) hw hv
  obtain ⟨hU, c, hcoord⟩ := common_ball_product_coordinates (fun p : V ↦ f p.1)
    r hr hc (fun p ↦ hV₂sub p.2.2) happ
  refine ⟨V, hpV, r, hr, hU, ?_, ?_, c, hcoord⟩
  · exact ⟨Metric.mem_ball_self hr, by rw [hzero]; exact Metric.mem_ball_self (by positivity)⟩
  · intro x
    exact (hcontrol x.1.1 x.1.2 (Metric.ball_subset_closedBall x.2.1)).1

end HolomorphicAnosov.Analysis

