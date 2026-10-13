import HolomorphicAnosov.Analysis.PullbackOperatorNormG11
import HolomorphicAnosov.Ghys.RealMetricAffinePlaque
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

noncomputable section
namespace HolomorphicAnosov.Ghys
open scoped Manifold ContDiff Bundle
open Set
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace
universe u v
variable {d : ℕ} {M : Type u} {L : Type v}
  [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M]
  [TopologicalSpace L] [ChartedSpace (Fin 2 → ℝ) L]

/-- For an immersed native real leaf and a differentiable complex development with positive pullback derivative norm N at p, the centered development N⁻¹(D−D(p)) has derivative norm one at p. (Ghys, Lemma 3.3) -/
lemma real_metric_development_norm_properties
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x))
    (j : L → M) (D : L → ℂ) (p : L)
    (hj : Function.Injective (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) j p)) :
    0 ≤ realMetricDevelopmentDerivativeNorm g j D p ∧
    (∀ v, ‖mvfderiv 𝓘(ℝ, Fin 2 → ℝ) D p v‖ ≤
      realMetricDevelopmentDerivativeNorm g j D p * realMetricLeafSpeed g j p v) ∧
    (mvfderiv 𝓘(ℝ, Fin 2 → ℝ) D p ≠ 0 →
      0 < realMetricDevelopmentDerivativeNorm g j D p) ∧
    (∀ c : ℝ, sSup ((fun v ↦ ‖c • mvfderiv 𝓘(ℝ, Fin 2 → ℝ) D p v‖) ''
        {v | realMetricLeafSpeed g j p v ≤ 1}) =
      |c| * realMetricDevelopmentDerivativeNorm g j D p) := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨g.toRiemannianMetric⟩
  let J := (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) j p).toLinearMap
  let T := (mvfderiv 𝓘(ℝ, Fin 2 → ℝ) D p).toLinearMap
  obtain ⟨N, hN, hsup, hbound, hpos, hscale⟩ := pullback_operator_norm (E := TangentSpace 𝓘(ℝ, Fin 2 → ℝ) p)
    (F := TangentSpace (realModel d) (j p)) J hj T
  have heq : N = realMetricDevelopmentDerivativeNorm g j D p := hsup
  subst N
  refine ⟨hN, hbound, ?_, hscale⟩
  intro hT
  apply hpos
  intro hz
  apply hT
  ext v
  exact congrArg (fun q : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) p →ₗ[ℝ] ℂ ↦ q v) hz

/-- Centering and dividing by the positive original-metric derivative norm gives unit norm. (Ghys, Lemma 3.3) -/
lemma real_metric_development_normalize
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x))
    (j : L → M) (D : L → ℂ) (p : L)
    (hj : Function.Injective (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) j p))
    (hD : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) D p)
    (hN : 0 < realMetricDevelopmentDerivativeNorm g j D p) :
    realMetricDevelopmentDerivativeNorm g j
      (fun y ↦ (realMetricDevelopmentDerivativeNorm g j D p)⁻¹ • (D y - D p)) p = 1 := by
  let N := realMetricDevelopmentDerivativeNorm g j D p
  have hd : mvfderiv 𝓘(ℝ, Fin 2 → ℝ) (fun y ↦ N⁻¹ • (D y - D p)) p =
      N⁻¹ • mvfderiv 𝓘(ℝ, Fin 2 → ℝ) D p := by
    change mvfderiv 𝓘(ℝ, Fin 2 → ℝ)
      ((fun _ : L ↦ N⁻¹) • (D - fun _ : L ↦ D p)) p = _
    rw [mvfderiv_smul mdifferentiableAt_const (hD.sub mdifferentiableAt_const),
      mvfderiv_sub hD mdifferentiableAt_const, mvfderiv_const, mvfderiv_const]
    simp
  change sSup ((fun v ↦ ‖mvfderiv 𝓘(ℝ, Fin 2 → ℝ)
    (fun y ↦ N⁻¹ • (D y - D p)) p v‖) '' {v | realMetricLeafSpeed g j p v ≤ 1}) = 1
  rw [hd]
  have hs := (real_metric_development_norm_properties g j D p hj).2.2.2 N⁻¹
  change sSup ((fun v ↦ ‖N⁻¹ • mvfderiv 𝓘(ℝ, Fin 2 → ℝ) D p v‖) ''
    {v | realMetricLeafSpeed g j p v ≤ 1}) = 1
  rw [hs]
  simpa only [N, abs_inv, abs_of_pos hN] using inv_mul_cancel₀ hN.ne'

end HolomorphicAnosov.Ghys
