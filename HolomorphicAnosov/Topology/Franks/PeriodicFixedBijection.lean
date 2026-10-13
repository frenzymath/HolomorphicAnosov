import HolomorphicAnosov.Topology.Franks.OriginalLiftUniqueFixedPoint
import HolomorphicAnosov.Topology.RealDisplacementEquivalence
import HolomorphicAnosov.Topology.HyperbolicPowerNotOne
import HolomorphicAnosov.Topology.IntegralMatrixPowerRealCast
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.Definitions

noncomputable section
namespace HolomorphicAnosov
open HolomorphicAnosov.Topology
/-- Projection intertwines each power of the real row action with the
corresponding iterate of the toral map. -/
theorem FranksOriginalLift.toral_iterate_projection {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ) (m : ℕ) (v : Fin n → ℝ) :
    coordinateProjection n ((((A : Matrix (Fin n) (Fin n) ℤ).map
      (Int.castRingHom ℝ)).mulVecLin ^ m) v) =
      (integralToralMap A)^[m] (coordinateProjection n v) := by
  have hp (v : Fin n → ℝ) : coordinateProjection n
      (((A : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℝ)).mulVecLin v) =
      integralToralMap A (coordinateProjection n v) := by
    ext i
    simp only [coordinateProjection, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, integralToralMap]
    simp only [← AddCircle.coe_zsmul, zsmul_eq_mul]
    exact map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) _ _
  rw [Module.End.pow_apply]
  exact (show Function.Semiconj (coordinateProjection n) _ (integralToralMap A)
    from hp).iterate_right m v

/-- The fixed points of every positive iterate of the hyperbolic toral map
are counted by its integral displacement determinant. Apply the real
displacement equivalence and the integer lattice quotient cardinality. -/
theorem FranksOriginalLift.toral_iterate_fixed_card {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hA : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ → ‖μ‖ ≠ 1)
    (m : ℕ) (hm : 0 < m) :
    Nat.card {y // (integralToralMap A)^[m] y = y} =
      (Matrix.det (1 - (A : Matrix (Fin n) (Fin n) ℤ)^m)).natAbs := by
  let R := (A : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℝ)
  let B := (R.mulVecLin ^ m).toContinuousLinearMap
  obtain ⟨L,hL⟩ := real_displacement_equivalence n A m
    (hyperbolic_power_not_one n _ hA m hm)
  let a : AddMonoid.End (UnitAddTorus (Fin n)) :=
    (show AddMonoid.End (UnitAddTorus (Fin n)) from Dynamics.integralToralAddHom A)^m
  have hp' : ∀ v, coordinateProjection n (B v) = a (coordinateProjection n v) :=
    fun v ↦ FranksOriginalLift.toral_iterate_projection A m v
  apply FranksOriginalLift.torus_fixed_card (1 - (A : Matrix (Fin n) (Fin n) ℤ)^m) B L a hL _ hp'
  intro z
  rw [hL, ← integral_matrix_power_real_cast]
  ext i
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Int.cast_sub]
  congr 1
  exact_mod_cast congrFun (congrArg (fun T : Module.End ℤ (Fin n → ℤ) ↦ T z)
    ((Matrix.toLin'_pow (A : Matrix (Fin n) (Fin n) ℤ) m).symm)) i
/-- Two periodic points have a common positive period, so same-period
injectivity gives injectivity on the entire periodic set. -/
theorem FranksOriginalLift.injOn_periodicPts_of_fixed_injective
    {X Y : Type*} (f : X → X) (h : X → Y)
    (hi : ∀ m : ℕ, 0 < m → ∀ x y, f^[m] x = x → f^[m] y = y → h x = h y → x = y) :
    Set.InjOn h (Function.periodicPts f) := by
  intro x hx y hy hxy
  obtain ⟨m, hm, hxm⟩ := hx
  obtain ⟨r, hr, hyr⟩ := hy
  exact hi (m*r) (Nat.mul_pos hm hr) x y
    (hxm.mul_const r) (hyr.const_mul m) hxy

/-- Existence of a preimage fixed at every positive target period gives
surjectivity between the periodic sets. -/
theorem FranksOriginalLift.surjOn_periodicPts_of_fixed_preimage
    {X Y : Type*} (f : X → X) (g : Y → Y) (h : X → Y)
    (ho : ∀ m : ℕ, 0 < m → ∀ y, g^[m] y = y → ∃ x, f^[m] x = x ∧ h x = y) :
    Set.SurjOn h (Function.periodicPts f) (Function.periodicPts g) := by
  intro y hy
  obtain ⟨m, hm, hym⟩ := hy
  obtain ⟨x, hx, hxy⟩ := ho m hm y hym
  exact ⟨x, ⟨m, hm, hx⟩, hxy⟩
end HolomorphicAnosov

