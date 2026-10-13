import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Paper.Zhang.OneParameterOrbitZero

/-! Injectivity at zero of orbit derivatives for free vector actions with smooth orbits. (Zhang, p.
13) -/

open scoped ContDiff

universe u v

namespace HolomorphicAnosov

attribute [local instance] complex_isManifold_real

/-- For a free vector action with real smooth orbit maps, the orbit derivative at zero has trivial
kernel. (Zhang, p. 13) -/
theorem vector_orbit_derivative_injective_zero
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} {M : Type v} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (A : V → Biholomorph d d M M)
    (hzero : ∀ x : M, A 0 x = x)
    (hadd : ∀ (a b : V) (x : M), A (a + b) x = A a (A b x))
    (hfree : ∀ (a : V) (x : M), A a x = x → a = 0) (x0 : M)
    (ho : ContMDiff (modelWithCornersSelf ℝ V) (realModel d) ∞
      (fun a : V ↦ A a x0)) :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ V) (realModel d)
      (fun a : V ↦ A a x0) 0) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  change v = 0
  let a : V := tangentSpaceCastModel (modelWithCornersSelf ℝ V) (0 : V) v
  let L : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight a
  have hc : ContMDiff (modelWithCornersSelf ℝ ℝ) (realModel d) ∞
      (fun t : ℝ ↦ A (t • a) x0) := ho.comp L.contMDiff
  have hc0 : mfderiv (modelWithCornersSelf ℝ ℝ) (realModel d)
      (fun t : ℝ ↦ A (t • a) x0) 0 = 0 := by
    have hline : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ V) L 0 := L.contMDiff.mdifferentiable (n := ∞) (by simp) 0
    have hchain := mfderiv_comp (I := modelWithCornersSelf ℝ ℝ)
      (I' := modelWithCornersSelf ℝ V) (I'' := realModel d) 0
      (ho.mdifferentiable (by simp) (L 0)) hline
    apply ContinuousLinearMap.ext
    intro r
    have he := congrArg (fun D ↦ D r) hchain
    have hlineD : mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ V) L 0 = L := by
      rw [mfderiv_eq_fderiv]
      exact L.hasFDerivAt.fderiv
    rw [hlineD] at he
    change (mfderiv (modelWithCornersSelf ℝ ℝ) (realModel d)
      (fun t : ℝ ↦ A (t • a) x0) 0) r = _ at he
    rw [he]
    have hL0 : L 0 = 0 := L.map_zero
    erw [hL0, ContinuousLinearMap.comp_apply]
    change (mfderiv (modelWithCornersSelf ℝ V) (realModel d)
      (fun a : V ↦ A a x0) 0)
      ((tangentSpaceCastModel (modelWithCornersSelf ℝ ℝ) (0 : ℝ) r) • v) = 0
    change (mfderiv (modelWithCornersSelf ℝ V) (realModel d)
      (fun a : V ↦ A a x0) 0) v = 0 at hv
    rw [map_smul, hv, smul_zero]

  have hconst := one_parameter_orbit_zero (fun t : ℝ ↦ A (t • a))
    (fun s t x ↦ by simpa only [add_smul] using hadd (s • a) (t • a) x)
    x0 hc hc0 1
  have ha : a = 0 := hfree a x0 (by simpa only [one_smul, zero_smul, hzero] using hconst)
  apply (tangentSpaceCastModel (modelWithCornersSelf ℝ V) (0 : V)).injective
  exact ha


end HolomorphicAnosov
