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
import HolomorphicAnosov.Paper.Zhang.VectorActionOrbitSmooth.ActualOneParameterGenerator
import HolomorphicAnosov.Paper.Zhang.VectorActionOrbitSmooth.ShiftedGeneratorDerivative
import HolomorphicAnosov.Paper.Zhang.VectorActionOrbitSmooth.GeneratorChartCoefficient
import HolomorphicAnosov.Paper.Zhang.VectorActionOrbitSmooth.GeneratorChartCoefficientSmooth
import HolomorphicAnosov.Paper.Zhang.VectorActionOrbitSmooth.GeneratorChartCoefficientDerivative
import HolomorphicAnosov.Paper.Zhang.VectorActionOrbitSmooth.SmoothOfNativePartials

/-! Real smoothness of orbit maps for continuous finite-dimensional vector actions by
biholomorphisms. (Zhang, Thm 3.3, p. 13; Bochner–Montgomery, Lemmas 2 and 5, Thm 4, eq. (27),
pp. 687–692; Demailly, I.3.B–C, pp. 22–23) -/

universe u v

namespace HolomorphicAnosov.Paper.Zhang

open scoped ContDiff Topology _root_.Topology


open Set Filter

set_option backward.isDefEq.respectTransparency false in
/-- Every orbit map of a continuous finite-dimensional real vector action by biholomorphisms is real
smooth. (Bochner–Montgomery, Lemmas 2 and 5, Thm 4, pp. 688–692; Zhang, p. 13; Demailly, I.3.C,
p. 23) -/
theorem vector_action_orbit_smooth
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {d : ℕ} {M : Type v} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (act : V → Biholomorph d d M M)
    (hzero : ∀ x : M, act 0 x = x)
    (hadd : ∀ v w : V, ∀ x : M, act (v + w) x = act v (act w x))
    (hcontinuous : Continuous (fun p : V × M ↦ act p.1 p.2)) :
    ∀ x : M, ContMDiff (modelWithCornersSelf ℝ V) (realModel d) ∞
      (fun v : V ↦ act v x) := by
  classical
  
  
  let := complex_isManifold_real d M
  let b := (Module.finBasis ℝ V).equivFunL
  let o : M → (Fin (Module.finrank ℝ V) → ℝ) → M := fun x v ↦ act (b.symm v) x
  let dir : Fin (Module.finrank ℝ V) → V := fun i ↦ b.symm (Pi.single i 1)
  have hg := fun i ↦ actual_one_parameter_generator act hzero hadd hcontinuous (dir i)
  choose X hX hd using hg
  intro x
  have ho : ContMDiff (modelWithCornersSelf ℝ (Fin (Module.finrank ℝ V) → ℝ))
      (realModel d) ∞ (o x) := by
    apply smooth_of_native_partials (o x)
      (hcontinuous.comp (b.symm.continuous.prodMk continuous_const)) X hX
    intro v i
    let a : ℝ → M → M := fun t y ↦ act (t • dir i) y
    have ha0 : ∀ y, a 0 y = y := by simpa [a] using hzero
    have haadd : ∀ s t y, a s (a t y) = a (s+t) y := by
      intro s t y
      simpa [a, add_smul] using (hadd (s • dir i) (t • dir i) y).symm
    have hv := shifted_generator_derivative a haadd (X i) (hd i) (o x v) 0
    have hsub := ((hasDerivAt_id (v i)).sub_const (v i)).hasFDerivAt.hasMFDerivAt
    have hv' : HasMFDerivAt (modelWithCornersSelf ℝ ℝ) (realModel d)
        (fun t ↦ a t (o x v)) ((fun t : ℝ ↦ t-v i) (v i))
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X i (a 0 (o x v)))) := by
      convert hv using 1
      first | rfl | simp
    have hh := hv'.comp (v i) (f := fun t : ℝ ↦ t-v i) hsub
    have heq : (fun t ↦ a (t-v i) (o x v)) =
        (fun t ↦ o x (Function.update v i t)) := by
      funext t
      dsimp [a,o]
      rw [← hadd]
      apply congrArg (fun v ↦ act v x)
      apply b.injective
      simp only [map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply, dir]
      ext j
      by_cases h : i = j
      · subst j
        simp
      · simp [Function.update, Ne.symm h]
    have hhh := hh.congr_of_eventuallyEq_abuse (Filter.Eventually.of_forall (congrFun heq.symm))
    apply hhh.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    change ℝ at r
    have hz : a 0 (o x v) = o x v := ha0 _
    change ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (X i (a 0 (o x v)))) ((ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)) r) : ComplexModel d) =
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (X i (o x v))) r : ComplexModel d)
    rw [hz]
    congr 1
    change r * 1 = r
    ring
  have hc := ho.comp b.contDiff.contMDiff
  simpa only [Function.comp_def, o, ContinuousLinearEquiv.symm_apply_apply] using hc




end HolomorphicAnosov.Paper.Zhang
