import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

open Set Filter MeasureTheory Manifold
open scoped ContDiff Manifold ENNReal Topology _root_.Topology Bundle

namespace HolomorphicAnosov.Proposition29Length

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A C¹ map whose tangent derivative is bounded by a positive constant `q` scales
Riemannian extended distance by at most `q`. (Zhang, Prop. 2.9) -/
theorem original_riemannianEDist_contraction
    (g : M → M) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 g)
    (q : ℝ) (hq : 0 < q)
    (hbound : ∀ x (v : TangentSpace 𝓘(ℝ, E) x),
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v‖ ≤ q * ‖v‖) (x y : M) :
    riemannianEDist 𝓘(ℝ, E) (g x) (g y) ≤
      ENNReal.ofReal q * riemannianEDist 𝓘(ℝ, E) x y := by
  have hq0 : ENNReal.ofReal q ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hq)
  conv_rhs => rw [riemannianEDist, ENNReal.mul_iInf_of_ne hq0 ENNReal.ofReal_ne_top]
  refine le_iInf fun γ ↦ ?_
  rw [ENNReal.mul_iInf_of_ne hq0 ENNReal.ofReal_ne_top]
  refine le_iInf fun hγ ↦ ?_
  let η : Path (g x) (g y) := γ.map hg.continuous
  have hη : ContMDiff (𝓡∂ 1) 𝓘(ℝ, E) 1 η := hg.comp hγ
  have hle : riemannianEDist 𝓘(ℝ, E) (g x) (g y) ≤
      ∫⁻ t, ‖mfderiv (𝓡∂ 1) 𝓘(ℝ, E) η t 1‖ₑ := by
    rw [riemannianEDist]
    exact iInf_le_of_le η (iInf_le_of_le hη le_rfl)
  refine hle.trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro t
  have hchain := mfderiv_comp t
    (hg.mdifferentiable one_ne_zero (γ t)) (hγ.mdifferentiable one_ne_zero t)
  change ‖mfderiv (𝓡∂ 1) 𝓘(ℝ, E) (g ∘ γ) t 1‖ₑ ≤ _
  rw [hchain, ContinuousLinearMap.comp_apply]
  simpa only [ENNReal.ofReal_mul hq.le, ofReal_norm] using
    ENNReal.ofReal_le_ofReal (hbound (γ t) (mfderiv (𝓡∂ 1) 𝓘(ℝ, E) γ t 1))


end HolomorphicAnosov.Proposition29Length
