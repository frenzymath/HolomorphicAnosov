import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Geometry.CurveConstantOfMfderivZero
import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.ComplexToRealMap

/-! An orbit of a one-parameter action is constant if its initial derivative vanishes. (Zhang, p.13) -/

open scoped ContDiff

universe u v

namespace HolomorphicAnosov

attribute [local instance] complex_isManifold_real

/-- A smooth orbit of a one-parameter biholomorphic action is constant if its derivative at zero
vanishes. (Lee (2003), Thm 17.8(d), pp.445–446, and Prop. 6.10, p.134; Zhang, p.13) -/
theorem one_parameter_orbit_zero
    {d : ℕ} {M : Type v} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (A : ℝ → Biholomorph d d M M)
    (hadd : ∀ (a b : ℝ) (x : M), A (a + b) x = A a (A b x))
    (x0 : M)
    (hc : ContMDiff (modelWithCornersSelf ℝ ℝ) (realModel d) ∞
      (fun t : ℝ ↦ A t x0))
    (h0 : mfderiv (modelWithCornersSelf ℝ ℝ) (realModel d)
      (fun t : ℝ ↦ A t x0) 0 = 0) :
    ∀ t, A t x0 = A 0 x0 := by
  apply fun t ↦ curve_constant_of_mfderiv_zero (fun t : ℝ ↦ A t x0) hc ?_ t 0
  intro t
  have hshift : (fun s : ℝ ↦ A (t + s) x0) = (A t) ∘ (fun s : ℝ ↦ A s x0) :=
    funext fun s ↦ hadd t s x0
  have hfixed := contMDiff_complex_to_real (A t).contMDiff
  have hcompose := mfderiv_comp (I := modelWithCornersSelf ℝ ℝ)
    (I' := realModel d) (I'' := realModel d) 0
    (hfixed.mdifferentiable (by simp) _) (hc.mdifferentiable (by simp) 0)
  rw [← hshift, h0, ContinuousLinearMap.comp_zero] at hcompose
  have htranslate : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) (fun s : ℝ ↦ t + s) 0 := by
    exact mdifferentiableAt_iff_differentiableAt.mpr (by fun_prop)
  have hchain := mfderiv_comp (I := modelWithCornersSelf ℝ ℝ)
    (I' := modelWithCornersSelf ℝ ℝ) (I'' := realModel d) 0
    (hc.mdifferentiable (by simp) (t + 0)) htranslate
  have htranslation : mfderiv (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) (fun s : ℝ ↦ t + s) 0 =
        ContinuousLinearMap.id ℝ _ := by
    rw [mfderiv_eq_fderiv]
    exact (hasFDerivAt_id 0).const_add t |>.fderiv
  rw [htranslation] at hchain
  erw [ContinuousLinearMap.comp_id] at hchain
  have hz := hchain.symm.trans hcompose
  erw [add_zero] at hz
  exact hz


end HolomorphicAnosov
