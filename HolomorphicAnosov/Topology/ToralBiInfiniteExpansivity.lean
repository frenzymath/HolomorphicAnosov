import HolomorphicAnosov.Linear.HyperbolicRealSplitting
import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import HolomorphicAnosov.Topology.IntegralToralMapSub
import HolomorphicAnosov.Topology.ShortIntegerLatticeVectorZero
import HolomorphicAnosov.Topology.TorusDisplacementHasNormBoundedLift
import HolomorphicAnosov.Topology.ShortToralLiftsExactRecurrence
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace HolomorphicAnosov

open Set

/-- Transfer the actual entrywise complex integer-matrix hypothesis to the exact
real scalar extension required by the existing hyperbolic splitting, then retain
its bounded-integer-orbit conclusion. Source: Alves Proposition4.1/Theorem5.5 and
Manning Lemma6 Step1. The Mathlib tensor coordinate equivalence is evaluated on
pure tensors: the SAME row-matrix acts on columns throughout. This parent-clause
proof uses the literal Mathlib real-matrix transport construction, with all helper
terms local; the lower splitting's pending proof remains an inherited dependency. -/
theorem hyperbolic_integer_matrix_bounded_orbit
    {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hhyper : ∀ μ : ℂ,
      Module.End.HasEigenvalue
        (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ → ‖μ‖ ≠ 1) :
    let T := (Matrix.GeneralLinearGroup.toLin
      (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A)).toLinearEquiv
    ∀ v : Fin n → ℝ, (∃ C : ℝ, ∀ k : ℤ, ‖(T ^ k) v‖ ≤ C) →
      ∀ k : ℤ, (T ^ k) v = 0 := by
  let T := (Matrix.GeneralLinearGroup.toLin
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A)).toLinearEquiv
  have hT : T.toLinearMap = Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℝ)) := rfl
  let e := TensorProduct.piScalarRight ℝ ℂ ℂ (Fin n)
  have htmul : ∀ (z : ℂ) (x : Fin n → ℝ),
      e (z ⊗ₜ[ℝ] x) = fun i ↦ (x i : ℂ) * z := by
    intro z x
    simp [e, Complex.real_smul]
  have hintertwine : ∀ w : TensorProduct ℝ ℂ (Fin n → ℝ),
      e (T.toLinearMap.baseChange ℂ w) =
        Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ)) (e w) := by
    intro w
    rw [hT]
    induction w using TensorProduct.inductionOn with
    | tmul z x =>
      simp only [LinearMap.baseChange_tmul, htmul]
      ext i
      change ((∑ j, (A i j : ℝ) * x j : ℝ) : ℂ) * z =
        ∑ j, (A i j : ℂ) * ((x j : ℂ) * z)
      simp [Finset.sum_mul, mul_assoc]
    | add w v hw hv => simp only [map_add, hw, hv]
  have hscalar : ∀ μ : ℂ,
      Module.End.HasEigenvalue (T.toLinearMap.baseChange ℂ) μ → ‖μ‖ ≠ 1 := by
    intro μ hμ
    apply hhyper μ
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := e w)
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨?_, ?_⟩
    · rw [← hintertwine, hw.apply_eq_smul]
      exact e.map_smul μ w
    · intro heq
      apply hw.2
      exact e.injective (heq.trans (map_zero e).symm)
  obtain ⟨Es, Eu, Ps, Pu, Cs, Cu, rs, ru, hall⟩ := hyperbolic_real_splitting n T hscalar
  rcases hall with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb⟩
  exact hb

/-- Uniform expansivity at the level of the actual target displacement orbit.
Source: Manning Lemma6 Step1, pp.427–428, with Alves' bounded integer-orbit conclusion.
Choose norm-bounded representatives at every integer time. The strict margin makes
all lattice discrepancies zero; genuine inverse recurrence identifies the negative
representatives with negative powers as well. The bounded-orbit theorem then kills
the initial representative. Empty target dimension requires no separate premise. -/
theorem small_biinfinite_toral_displacement_zero
    {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hhyper : ∀ μ : ℂ,
      Module.End.HasEigenvalue
        (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ → ‖μ‖ ≠ 1) :
    ∃ e : ℝ, 0 < e ∧ ∀ d : ℤ → UnitAddTorus (Fin n),
      (∀ j : ℤ, d (j + 1) = integralToralMap A (d j)) →
      (∀ j : ℤ, ‖d j‖ ≤ e) → d 0 = 0 := by
  classical
  let T := (Matrix.GeneralLinearGroup.toLin
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A)).toLinearEquiv
  let Tc := T.toContinuousLinearEquiv.toContinuousLinearMap
  have hTc : Tc =
      (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℝ))).toContinuousLinearMap := rfl
  let e : ℝ := 1 / (2 * (‖Tc‖ + 1))
  have he : 0 < e := by dsimp [e]; positivity
  have hsmall : (‖Tc‖ + 1) * e < 1 := by
    dsimp [e]
    have hpos : 0 < ‖Tc‖ + 1 := by positivity
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith
  refine ⟨e, he, ?_⟩
  intro d hrec hnorm
  choose v hvquot hvnorm using fun j : ℤ ↦ torus_displacement_has_norm_bounded_lift (d j)
  have hvsmall : ∀ j : ℤ, ‖v j‖ ≤ e := fun j ↦ (hvnorm j).trans (hnorm j)
  have hvrec : ∀ j : ℤ, v (j + 1) = T (v j) := by
    intro j
    have hquot : (fun i ↦ (v (j + 1) i : UnitAddCircle)) =
        integralToralMap A (fun i ↦ (v j i : UnitAddCircle)) := by
      have hqnext : (fun i ↦ (v (j + 1) i : UnitAddCircle)) = d (j + 1) := funext (hvquot _)
      have hqnow : (fun i ↦ (v j i : UnitAddCircle)) = d j := funext (hvquot _)
      rw [hqnext, hqnow, hrec]
    have hexact := short_toral_lifts_exact_recurrence A (v j) (v (j + 1)) e
      (hvsmall j) (hvsmall (j + 1)) hquot
    have hs : (‖(Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℝ))).toContinuousLinearMap‖
        + 1) * e < 1 := by rw [← hTc]; exact hsmall
    exact hexact hs
  have hvpow : ∀ j : ℤ, v j = (T ^ j) (v 0) := by
    intro j
    induction j using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [hvrec, ih]
      have hp : T * T ^ (k : ℤ) = T ^ ((k : ℤ) + 1) := by
        rw [← zpow_one_add]
        congr 1
        omega
      change (T * T ^ (k : ℤ)) (v 0) = _
      rw [hp]
    | pred k ih =>
      apply T.injective
      have hr : T (v (-(k : ℤ) - 1)) = v (-(k : ℤ)) := by
        have := hvrec (-(k : ℤ) - 1)
        simpa only [sub_add_cancel] using this.symm
      rw [hr, ih]
      have hp : T * T ^ (-(k : ℤ) - 1) = T ^ (-(k : ℤ)) := by
        rw [← zpow_one_add]
        congr 1
        omega
      change _ = (T * T ^ (-(k : ℤ) - 1)) (v 0)
      rw [hp]
  have hzero : v 0 = 0 := by
    have hb := hyperbolic_integer_matrix_bounded_orbit A hhyper (v 0)
      ⟨e, fun j ↦ by rw [← hvpow]; exact hvsmall j⟩ 0
    simpa using hb
  funext i
  rw [← hvquot 0 i, hzero]
  rfl

/-- Actual uniform target expansivity for two bi-infinite toral orbits, with the
same integer row-matrix and the native finite-product quotient metric. Source:
Manning Lemma6 Step1, pp.427–428, and the exact lifted-orbit proof above. Take the
pointwise difference, use additivity, and apply the proved short-displacement
exclusion. The conclusion includes n=0 and uses no source smooth structure. -/
theorem integral_toral_biinfinite_expansivity
    {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hhyper : ∀ μ : ℂ,
      Module.End.HasEigenvalue
        (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ → ‖μ‖ ≠ 1) :
    ∃ e : ℝ, 0 < e ∧ ∀ u v : ℤ → UnitAddTorus (Fin n),
      (∀ j : ℤ, u (j + 1) = integralToralMap A (u j)) →
      (∀ j : ℤ, v (j + 1) = integralToralMap A (v j)) →
      (∀ j : ℤ, dist (u j) (v j) ≤ e) → u 0 = v 0 := by
  obtain ⟨e, he, hexclude⟩ := small_biinfinite_toral_displacement_zero A hhyper
  refine ⟨e, he, ?_⟩
  intro u v hu hv hdist
  have hzero := hexclude (fun j ↦ u j - v j) (fun j ↦ by
    rw [hu, hv, integral_toral_map_sub]) (fun j ↦ by
      simpa only [dist_eq_norm] using hdist j)
  exact sub_eq_zero.mp hzero


end HolomorphicAnosov
