import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.Manifold.OneParameterSmoothGenerator
import HolomorphicAnosov.Geometry.Manifold.VectorActionSpatialDerivativesContinuous
import HolomorphicAnosov.Geometry.Biholomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Paper.Zhang.VectorActionOrbitSmooth.SmoothOfSmoothDerivativeCoefficients
import HolomorphicAnosov.Paper.Zhang.VectorActionOrbitSmooth.PartialDerivativeMap
import HolomorphicAnosov.Paper.Zhang.VectorActionOrbitSmooth.HasFDerivAtOfContinuousPartials
import HolomorphicAnosov.Paper.Zhang.VectorActionOrbitSmooth.GeneratorChartCoefficient
import HolomorphicAnosov.Paper.Zhang.VectorActionOrbitSmooth.GeneratorChartCoefficientSmooth
import HolomorphicAnosov.Paper.Zhang.VectorActionOrbitSmooth.GeneratorChartCoefficientDerivative

universe u v
namespace HolomorphicAnosov.Paper.Zhang
open scoped ContDiff Topology _root_.Topology
open Set Filter

set_option backward.isDefEq.respectTransparency false in
/-- A continuous manifold-valued map whose coordinate partials are given by smooth tangent vector
fields is smooth. (Bochner–Montgomery, Thm 4, eq. (27), pp. 691–692) -/
theorem smooth_of_native_partials
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
    (o : (Fin n → ℝ) → M) (hc : Continuous o)
    (X : Fin n → (x : M) → TangentSpace (modelWithCornersSelf ℝ E) x)
    (hX : ∀ i, ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E).tangent ∞
      (fun x ↦ (⟨x,X i x⟩ : TangentBundle (modelWithCornersSelf ℝ E) M)))
    (hd : ∀ v i, HasMFDerivAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ E)
      (fun t ↦ o (Function.update v i t)) (v i)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X i (o v)))) :
    ContMDiff (modelWithCornersSelf ℝ (Fin n → ℝ)) (modelWithCornersSelf ℝ E) ∞ o := by
  intro v₀
  let p := o v₀
  let e := extChartAt (modelWithCornersSelf ℝ E) p
  let s := o ⁻¹' e.source
  let f : (Fin n → ℝ) → E := fun v ↦ e (o v)
  let B : E → (Fin n → ℝ) →L[ℝ] E :=
    fun y ↦ partialDerivativeMap (fun i ↦ generatorChartCoefficient p (X i) y)
  have hs : IsOpen s := by
    exact ((isOpen_extChartAt_source (I := modelWithCornersSelf ℝ E) p)).preimage hc
  have hv₀ : v₀ ∈ s := mem_extChartAt_source p
  have hmap : MapsTo f s e.target := fun v hv ↦ e.map_source hv
  have hfcont : ContinuousOn f s := (continuousOn_extChartAt p).comp hc.continuousOn
    (fun _ hv ↦ hv)
  have hB : ContDiffOn ℝ ∞ B e.target := by
    apply ContDiffOn.sum
    intro i hi
    exact (ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) E
      (ContinuousLinearMap.proj i)).contDiff.comp_contDiffOn
        (generatorChartCoefficient_smooth p (X i) (hX i))
  have hdf : ∀ v ∈ s, HasFDerivAt f (B (f v)) v := by
    apply hasFDerivAt_of_continuous_partials hs
    · intro i
      exact (generatorChartCoefficient_smooth p (X i) (hX i)).continuousOn.comp hfcont hmap
    · intro v hv i
      have hh := generatorChartCoefficient_derivative p (X i)
        (fun t ↦ o (Function.update v i t)) (v i) (by simpa [s, e] using hv) (by
          convert hd v i using 1
          apply ContinuousLinearMap.ext
          intro a
          change a • (X i (o (Function.update v i (v i))) : E) = a • (X i (o v) : E)
          rw [Function.update_eq_self])
      simpa only [f, e, Function.update_eq_self i v] using hh
  have hf : ContDiffOn ℝ ∞ f s := smooth_of_smooth_derivative_coefficients hs
    (by exact isOpen_extChartAt_target p) hmap hB hdf
  have ho := (contMDiffOn_extChartAt_symm p).comp hf.contMDiffOn hmap
  have heq : EqOn (e.symm ∘ f) o s := fun v hv ↦ e.left_inv hv
  exact (ho.congr heq.symm v₀ hv₀).contMDiffAt (hs.mem_nhds hv₀)


end HolomorphicAnosov.Paper.Zhang
