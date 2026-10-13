import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Paper.Zhang.VectorOrbitDerivativeInjectiveZero

/-! Injectivity of orbit derivatives for free vector actions with smooth orbits. (Zhang, p. 13) -/

open scoped ContDiff

universe u v

namespace HolomorphicAnosov

attribute [local instance] complex_isManifold_real

/-- For a free vector action with real smooth orbit maps, the orbit derivative is injective at every
parameter. (Zhang, p. 13) -/
theorem vector_orbit_derivative_injective
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} {M : Type v} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (A : V → Biholomorph d d M M)
    (hzero : ∀ x : M, A 0 x = x)
    (hadd : ∀ (a b : V) (x : M), A (a + b) x = A a (A b x))
    (hfree : ∀ (a : V) (x : M), A a x = x → a = 0)
    (ho : ∀ x0 : M, ContMDiff (modelWithCornersSelf ℝ V) (realModel d) ∞
      (fun a : V ↦ A a x0)) (x0 : M) (v : V) :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ V) (realModel d)
      (fun a : V ↦ A a x0) v) := by
  have hshift : (fun w : V ↦ A (w + v) x0) = (fun w : V ↦ A w (A v x0)) :=
    funext fun w ↦ hadd w v x0
  have htranslate : MDifferentiableAt (modelWithCornersSelf ℝ V)
      (modelWithCornersSelf ℝ V) (fun w : V ↦ w + v) 0 :=
    mdifferentiableAt_iff_differentiableAt.mpr (by fun_prop)
  have hchain := mfderiv_comp (I := modelWithCornersSelf ℝ V)
    (I' := modelWithCornersSelf ℝ V) (I'' := realModel d) 0
    ((ho x0).mdifferentiable (by simp) (0 + v)) htranslate
  have htranslation : mfderiv (modelWithCornersSelf ℝ V)
      (modelWithCornersSelf ℝ V) (fun w : V ↦ w + v) 0 =
        ContinuousLinearMap.id ℝ _ := by
    rw [mfderiv_eq_fderiv]
    exact (hasFDerivAt_id (0 : V)).add_const v |>.fderiv
  rw [htranslation] at hchain
  erw [ContinuousLinearMap.comp_id, zero_add] at hchain
  change mfderiv (modelWithCornersSelf ℝ V) (realModel d)
    (fun w : V ↦ A (w + v) x0) 0 = _ at hchain
  have hinj := vector_orbit_derivative_injective_zero A hzero hadd hfree
    (A v x0) (ho (A v x0))
  rw [← hshift] at hinj
  rw [hchain] at hinj
  exact hinj


end HolomorphicAnosov
