import HolomorphicAnosov.Geometry.HPSRealAnosovEstimateDataG8
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.mfderiv_iterate_fixed
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.inverse_derivative_left
import HolomorphicAnosov.Dynamics.Anosov.IterateInvariant
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import HolomorphicAnosov.Topology.Franks.UnitProductNoExponentialLimit
import HolomorphicAnosov.Topology.Franks.ChartLocalIndex
import HolomorphicAnosov.Topology.Franks.SubbundleOrientation
import Mathlib.Analysis.SpecificLimits.Normed

open Filter TopologicalSpace
open scoped _root_.Topology ContDiff Bundle
namespace HolomorphicAnosov.FranksPeriodicDerivative
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

omit [IsManifold I ∞ X] in
/-- At a point fixed by a positive iterate, the original all-time contraction
bounds imply decay of powers of that iterate's actual tangent derivative.
The chain rule identifies those powers with the original times m*k. -/
theorem periodic_derivative_decay_of_bounds
    (f : Diffeomorph I I X X ∞)
    [Bundle.RiemannianBundle (fun y : X ↦ TangentSpace I y)]
    (m : ℕ) (hm : 0 < m) (x : X) (hx : (realIterate I f m) x = x)
    (v : TangentSpace I x) (C r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hb : ∀ k : ℕ, ‖mfderiv I I (realIterate I f k) x v‖ ≤ C*r^k*‖v‖) :
    Tendsto (fun k : ℕ ↦
      ((show TangentSpace I x →L[ℝ] TangentSpace I x from
        mfderiv I I (realIterate I f m) x)^k) v) atTop (𝓝 0) := by
  let g := realIterate I f m
  have hfun (k : ℕ) : (g : X → X)^[k] = (realIterate I f (m*k) : X → X) := by
    exact (Function.iterate_mul (f : X → X) m k).symm
  have hfix (k : ℕ) : (realIterate I f (m*k)) x = x := by
    rw [← hfun]
    exact Function.iterate_fixed hx k
  have hbound (k : ℕ) :
      ‖((show TangentSpace I x →L[ℝ] TangentSpace I x from mfderiv I I g x)^k) v‖ ≤
        C*(r^m)^k*‖v‖ := by
    rw [← TheoremAProof.mfderiv_iterate_fixed g x hx k]
    have h := hb (m*k)
    rw [pow_mul] at h
    have hder := mfderiv_congr (I := I) (I' := I) (x := x) (hfun k)
    have hnorm : @Norm.norm (TangentSpace I ((realIterate I f (m*k)) x)) inferInstance =
        @Norm.norm (TangentSpace I x) inferInstance := by rw [hfix k]
    rw [hnorm] at h
    rw [hder]
    exact h
  apply squeeze_zero_norm hbound
  have hrm : r^m < 1 := pow_lt_one₀ hr hr1 (Nat.ne_of_gt hm)
  simpa using (tendsto_const_nhds.mul
    (tendsto_pow_atTop_nhds_zero_of_lt_one (pow_nonneg hr m) hrm)).mul_const ‖v‖


end
end HolomorphicAnosov.FranksPeriodicDerivative


namespace HolomorphicAnosov.FranksPeriodicDerivative
noncomputable section
open Filter
open scoped _root_.Topology ContDiff Bundle
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- At a periodic point, the backward iterate derivative on the original
unstable fibre has decaying powers. This is the direct inverse-time form of the
supplied Anosov estimate and avoids identifying unequal tangent fibres until a
separate derivative inverse lemma is applied. -/
theorem unstable_backward_return_derivative_decay
    (f : Diffeomorph I I X X ∞)
    [Bundle.RiemannianBundle (fun y : X ↦ TangentSpace I y)]
    (S : InvariantRealTangentSplitting f) (hb : BundleAnosovBounds f S)
    (m : ℕ) (hm : 0 < m) (x : X) (hx : (realIterate I f m) x = x) :
    ∀ v : TangentSpace I x, v ∈ S.unstable.toDistribution x →
      Tendsto (fun k : ℕ ↦
        ((show TangentSpace I x →L[ℝ] TangentSpace I x from
          mfderiv I I (realIterate I f.symm m) x)^k) v) atTop (𝓝 0) := by
  obtain ⟨C,r,hC,hr,hr1,hs,hu⟩ := hb
  have hxi : (realIterate I f.symm m) x = x := by
    apply (realIterate I f m).injective
    exact (Diffeomorph.apply_symm_apply _ _).trans hx.symm
  intro v hv
  apply periodic_derivative_decay_of_bounds f.symm m hm x hxi v C r hr.le hr1
  intro k
  exact hu k x v hv

omit [IsManifold I ∞ X] in
/-- The derivative of the backward return is the inverse of the forward return
at a periodic point. Apply the chain-rule left inverse to a preimage under the
actual derivative equivalence; surjectivity supplies that preimage. -/
theorem return_inverse_derivative (f : Diffeomorph I I X X ∞) (m:ℕ) (x:X)
 (hx : (realIterate I f m) x = x) :
 mfderiv I I (realIterate I f.symm m) x =
 (mfderiv I I (realIterate I f m) x).inverse := by
 let g := realIterate I f m
 have hxi : (realIterate I f.symm m) x = x := by
   apply g.injective
   exact (Diffeomorph.apply_symm_apply _ _).trans hx.symm
 have h := TheoremAProof.inverse_derivative_left g x
 rw [hx] at h
 have hi : (g.mfderivToContinuousLinearEquiv (by simp) x).toContinuousLinearMap = mfderiv I I g x := rfl
 rw [← hi] at h
 let T := g.mfderivToContinuousLinearEquiv (by simp) x
 apply ContinuousLinearMap.ext
 intro z
 obtain ⟨w, hw⟩ := T.surjective z
 subst z
 have hz := congrArg (fun A : TangentSpace I x →L[ℝ] TangentSpace I x => A w) h
 change mfderiv I I g.symm x (T w) = w at hz
 exact hz.trans ((g.isInvertible_mfderiv (by simp)).inverse_apply_eq.mpr rfl).symm

/-- The actual original periodic derivative restricts to the stable and unstable
fibres. Forward stable and inverse unstable powers decay in their inherited norms. -/
theorem original_periodic_derivative_blocks
    (f : Diffeomorph I I X X ∞)
    [Bundle.RiemannianBundle (fun y : X ↦ TangentSpace I y)]
    (S : InvariantRealTangentSplitting f) (hb : BundleAnosovBounds f S)
    (m : ℕ) (hm : 0 < m) (x : X) (hx : (realIterate I f m) x = x) :
    ∃ (T : TangentSpace I x ≃L[ℝ] TangentSpace I x)
      (TS : S.stable.toDistribution x ≃L[ℝ] S.stable.toDistribution x)
      (TU : S.unstable.toDistribution x ≃L[ℝ] S.unstable.toDistribution x),
      T.toContinuousLinearMap =
        (show TangentSpace I x →L[ℝ] TangentSpace I x from mfderiv I I (realIterate I f m) x) ∧
      (∀ v, (TS v : TangentSpace I x) = T v) ∧
      (∀ v, (TU v : TangentSpace I x) = T v) ∧
      (∀ v, Tendsto (fun k : ℕ ↦ (TS.toContinuousLinearMap^k) v) atTop (𝓝 0)) ∧
      (∀ v, Tendsto (fun k : ℕ ↦ (TU.symm.toContinuousLinearMap^k) v) atTop (𝓝 0)) := by
  let g := realIterate I f m
  let T : TangentSpace I x ≃L[ℝ] TangentSpace I x :=
    g.mfderivToContinuousLinearEquiv (by simp) x
  have hx' : (f : X → X)^[m] x = x := hx
  have hS : (S.stable.toDistribution x).map T.toLinearMap = S.stable.toDistribution x := by
    have h := real_distribution_iterate_invariant f _ S.stable_map m x
    erw [hx'] at h
    exact h
  have hU : (S.unstable.toDistribution x).map T.toLinearMap = S.unstable.toDistribution x := by
    have h := real_distribution_iterate_invariant f _ S.unstable_map m x
    erw [hx'] at h
    exact h
  let TS := T.ofSubmodules _ _ hS
  let TU := T.ofSubmodules _ _ hU
  have hTS (v : S.stable.toDistribution x) (k : ℕ) :
      ((TS.toContinuousLinearMap^k) v : TangentSpace I x) =
        (T.toContinuousLinearMap^k) v := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [pow_succ', mul_apply_eq_comp]
      change T ((TS.toContinuousLinearMap^k) v) = T ((T.toContinuousLinearMap^k) v)
      rw [ih]
  have hTU (v : S.unstable.toDistribution x) (k : ℕ) :
      ((TU.symm.toContinuousLinearMap^k) v : TangentSpace I x) =
        (T.symm.toContinuousLinearMap^k) v := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [pow_succ', mul_apply_eq_comp]
      change T.symm ((TU.symm.toContinuousLinearMap^k) v) = T.symm ((T.symm.toContinuousLinearMap^k) v)
      rw [ih]
  have hi : T.symm.toContinuousLinearMap =
      (show TangentSpace I x →L[ℝ] TangentSpace I x from
        mfderiv I I (realIterate I f.symm m) x) := by
    have h := return_inverse_derivative f m x hx
    have he : T.toContinuousLinearMap.inverse = T.symm.toContinuousLinearMap :=
      ContinuousLinearMap.inverse_equiv T
    exact he.symm.trans h.symm
  obtain ⟨C,r,hC,hr,hr1,hs,hu⟩ := hb
  refine ⟨T,TS,TU,rfl,fun _ ↦ rfl,fun _ ↦ rfl,?_,?_⟩
  · intro v
    have h := periodic_derivative_decay_of_bounds f m hm x hx v.val C r hr.le hr1
      (fun k ↦ hs k x v.val v.property)
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun k ↦ ((TS.toContinuousLinearMap^k) v : TangentSpace I x)) atTop (𝓝 (0 : TangentSpace I x))
    simp_rw [hTS]
    exact h
  · intro v
    have h := unstable_backward_return_derivative_decay f S
      ⟨C,r,hC,hr,hr1,hs,hu⟩ m hm x hx v.val v.property
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun k ↦ ((TU.symm.toContinuousLinearMap^k) v : TangentSpace I x)) atTop (𝓝 (0 : TangentSpace I x))
    simp_rw [hTU, hi]
    exact h

/-- The return displacement is nonsingular, and its determinant has the
unstable orientation sign times the parity of unstable dimension. -/
theorem original_periodic_displacement_factor [FiniteDimensional ℝ E]
    (f : Diffeomorph I I X X ∞)
    [Bundle.RiemannianBundle (fun y : X ↦ TangentSpace I y)]
    (S : InvariantRealTangentSplitting f) (hb : BundleAnosovBounds f S)
    (m : ℕ) (hm : 0 < m) (x : X) (hx : (realIterate I f m) x = x) :
    ∃ (TU : S.unstable.toDistribution x ≃L[ℝ] S.unstable.toDistribution x),
      (∀ v, (TU v : TangentSpace I x) = mfderiv I I (realIterate I f m) x v) ∧
      ∃ c : ℝ, 0 < c ∧
        LinearMap.det (1-(show TangentSpace I x →L[ℝ] TangentSpace I x from
          mfderiv I I (realIterate I f m) x).toLinearMap) =
          (-1:ℝ)^(Module.finrank ℝ (S.unstable.toDistribution x))*LinearMap.det TU.toLinearMap*c := by
  obtain ⟨T,TS,TU,hT,hTS,hTU,hs,hu⟩ := original_periodic_derivative_blocks f S hb m hm x hx
  obtain ⟨c,hc,he⟩ := linear_det_invariant_splitting_factor T.toContinuousLinearMap
    (S.stable.toDistribution x) (S.unstable.toDistribution x) (S.isCompl x)
    TS.toContinuousLinearMap TU hTS hTU hs hu
  refine ⟨TU, ?_, c,hc, ?_⟩
  · intro v
    exact (hTU v).trans (congrArg (fun A : TangentSpace I x →L[ℝ] TangentSpace I x ↦ A v) hT)
  · simpa only [hT] using he

/-- A nonsingular finite-dimensional continuous linear endomorphism has its
actual continuous linear inverse. -/
theorem invertible_of_det_ne_zero {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (D : V →L[ℝ] V)
    (hD : LinearMap.det D.toLinearMap ≠ 0) : D.IsInvertible := by
  obtain ⟨u,hu⟩ := (LinearMap.isUnit_iff_isUnit_det D.toLinearMap).mpr
    (isUnit_iff_ne_zero.mpr hD)
  let A := (LinearMap.GeneralLinearGroup.toLinearEquiv u).toContinuousLinearEquiv
  refine ⟨A, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun L : V →ₗ[ℝ] V ↦ L v) hu

/-- At an original Anosov periodic point the canonical local index is the
unstable return orientation sign times the parity of unstable rank. -/
theorem original_periodic_index {n : ℕ} {M : Type*}
    [TopologicalSpace M] [MetrizableSpace M] [LocallyCompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (S : InvariantRealTangentSplitting f) (hb : BundleAnosovBounds f S)
    (m : ℕ) (hm : 0 < m) (x : M) (hx : (realIterate _ f m) x = x)
    (e : FixedPointIndexInterface.ENRRepresentation M)
    (hfinite : {y : M | (realIterate _ f m) y = y}.Finite) :
    ∃ TU : S.unstable.toDistribution x ≃L[ℝ] S.unstable.toDistribution x,
      (∀ v, (TU v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x) =
        mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (realIterate _ f m) x v) ∧
      FixedPointIndexInterface.finiteFixedPointLocalIndex e
        ⟨realIterate _ f m, (realIterate _ f m).continuous⟩ hfinite x =
          (-1:ℤ)^(Module.finrank ℝ (S.unstable.toDistribution x)) *
            (SignType.sign (LinearMap.det TU.toLinearMap) : ℤ) := by
  let J := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))
  obtain ⟨TU,hTU,c,hc,he⟩ := original_periodic_displacement_factor f S hb m hm x hx
  let D : TangentSpace J x →L[ℝ] TangentSpace J x :=
    1-(show TangentSpace J x →L[ℝ] TangentSpace J x from mfderiv J J (realIterate J f m) x)
  have hD : LinearMap.det D.toLinearMap ≠ 0 := by
    rw [show D.toLinearMap = 1-(show TangentSpace J x →L[ℝ] TangentSpace J x from
      mfderiv J J (realIterate J f m) x).toLinearMap from rfl, he]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      TU.toLinearEquiv.isUnit_det'.ne_zero) hc.ne'
  have hi := FixedPointIndexInterface.finite_local_index_of_tangent_displacement e
    (⟨realIterate J f m, (realIterate J f m).continuous⟩ : C(M,M)) hfinite x hx
    ((realIterate J f m).contMDiff.mdifferentiableAt (by simp)) D rfl
    (invertible_of_det_ne_zero D hD)
  refine ⟨TU,hTU,hi.trans ?_⟩
  change (SignType.sign (LinearMap.det (1-(show TangentSpace J x →L[ℝ] TangentSpace J x from
    mfderiv J J (realIterate J f m) x).toLinearMap)) : ℤ) = _
  rw [he]
  simp [sign_mul, sign_pow, sign_eq_one_iff.mpr hc]

/-- Every fixed point of a lift of an original Anosov return has local index
(-1)^u times the determinant sign of its original unstable return derivative. -/
theorem lifted_periodic_index {n : ℕ} {M Y : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [TopologicalSpace Y] [MetrizableSpace Y] [LocallyCompactSpace Y]
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    [Bundle.RiemannianBundle (fun y : M ↦ TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) y)]
    (S : InvariantRealTangentSplitting f) (hb : BundleAnosovBounds f S)
    (m : ℕ) (hm : 0 < m) (F : C(Y, Y))
    (p : Y → M) (hp : IsLocalHomeomorph p)
    (hF : ∀ y, p (F y) = (realIterate _ f m) (p y))
    (x : Y) (hx : F x = x) (e : FixedPointIndexInterface.ENRRepresentation Y)
    (hfinite : {y : Y | F y = y}.Finite) :
    ∃ TU : S.unstable.toDistribution (p x) ≃L[ℝ] S.unstable.toDistribution (p x),
      (∀ v, (TU v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (p x)) =
        mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (realIterate _ f m) (p x) v) ∧
      FixedPointIndexInterface.finiteFixedPointLocalIndex e F hfinite x =
        (-1:ℤ)^(Module.finrank ℝ (S.unstable.toDistribution (p x))) *
          (SignType.sign (LinearMap.det TU.toLinearMap) : ℤ) := by
  let J := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))
  have hpx : (realIterate J f m) (p x) = p x := (hF x).symm.trans (congrArg p hx)
  obtain ⟨TU,hTU,c,hc,he⟩ := original_periodic_displacement_factor f S hb m hm (p x) hpx
  let D : TangentSpace J (p x) →L[ℝ] TangentSpace J (p x) :=
    1-(show TangentSpace J (p x) →L[ℝ] TangentSpace J (p x) from mfderiv J J (realIterate J f m) (p x))
  have hD : LinearMap.det D.toLinearMap ≠ 0 := by
    rw [show D.toLinearMap = 1-(show TangentSpace J (p x) →L[ℝ] TangentSpace J (p x) from
      mfderiv J J (realIterate J f m) (p x)).toLinearMap from rfl, he]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      TU.toLinearEquiv.isUnit_det'.ne_zero) hc.ne'
  have hi := FixedPointIndexInterface.finite_local_index_of_cover_tangent e F
    (⟨realIterate J f m, (realIterate J f m).continuous⟩ : C(M,M)) hfinite x hx p hp hF
    ((realIterate J f m).contMDiff.mdifferentiableAt (by simp)) D rfl
    (invertible_of_det_ne_zero D hD)
  refine ⟨TU,hTU,hi.trans ?_⟩
  change (SignType.sign (LinearMap.det (1-(show TangentSpace J (p x) →L[ℝ] TangentSpace J (p x) from
    mfderiv J J (realIterate J f m) (p x)).toLinearMap)) : ℤ) = _
  rw [he]
  simp [sign_mul, sign_pow, sign_eq_one_iff.mpr hc]

/-- A lift of any positive Anosov iterate to the doubled torus cover has one
common unit local index at every fixed point. -/
theorem doubled_lift_index_constant {n : ℕ} {M : Type*}
    [TopologicalSpace M] [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    (q : M ≃ₜ UnitAddTorus (Fin n))
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    [Bundle.RiemannianBundle (fun y : M ↦ TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) y)]
    (S : InvariantRealTangentSplitting f) (hb : BundleAnosovBounds f S)
    (m : ℕ) (hm : 0 < m) (F : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)))
    (hF : ∀ y, q.symm (2 • F y) = (realIterate _ f m) (q.symm (2 • y)))
    (e : FixedPointIndexInterface.ENRRepresentation (UnitAddTorus (Fin n)))
    (hfinite : {y | F y = y}.Finite) :
    ∃ ε : ℤˣ, ∀ x, F x = x →
      FixedPointIndexInterface.finiteFixedPointLocalIndex e F hfinite x = (ε : ℤ) := by
  let J := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))
  let p := fun y : UnitAddTorus (Fin n) ↦ q.symm (2 • y)
  let d := Module.finrank ℝ (S.unstable.toDistribution (q.symm 0))
  have hInv : ∀ x, (S.unstable.toDistribution x).map
      (mfderiv J J (realIterate J f m) x).toLinearMap =
        S.unstable.toDistribution ((realIterate J f m) x) :=
    real_distribution_iterate_invariant f _ S.unstable_map m
  obtain ⟨o,L,hL,hconst⟩ := FranksSubbundleOrientation.doubled_derivative_comparison_constant
    q S.unstable (realIterate J f m) hInv F hF
  let ε := (-1 : ℤˣ)^d * realOrientationComparison d (L 0).toLinearEquiv (o 0) (o (F 0))
  refine ⟨ε, ?_⟩
  intro x hx
  have hp : IsLocalHomeomorph p :=
    ((Topology.FranksCover.nsmul_cover n 2 (by omega)).homeomorph_comp q.symm).isLocalHomeomorph
  obtain ⟨TU,hTU,hi⟩ := lifted_periodic_index f S hb m hm F p hp hF x hx e hfinite
  have hc := FranksSubbundleOrientation.comparison_of_tangent_action
    S.unstable.toDistribution p d o x (F x) hx (L x).toLinearEquiv TU.toLinearEquiv (by
      intro v
      have h := (hL x v).trans (hTU v).symm
      exact h)
  rw [hi, ← hc, hconst x 0, S.unstable.finrank_eq (p x) (q.symm 0)]
  simp [ε, d]

end
end HolomorphicAnosov.FranksPeriodicDerivative

