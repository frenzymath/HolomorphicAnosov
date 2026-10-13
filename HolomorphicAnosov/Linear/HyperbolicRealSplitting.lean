import HolomorphicAnosov.Linear.HyperbolicDecayComplement
import HolomorphicAnosov.Linear.HyperbolicRealSplitting.TendstoCLMZeroOfPointwise
import HolomorphicAnosov.Linear.HyperbolicRealSplitting.PowApplyNormLe
import HolomorphicAnosov.Linear.HyperbolicRealSplitting.ExponentialOfDecay
import HolomorphicAnosov.Linear.HyperbolicRealSplitting.DecayInvariant
import HolomorphicAnosov.Linear.HyperbolicRealSplitting.RestrictedExponential
import HolomorphicAnosov.Linear.InvariantComplementProjection
import HolomorphicAnosov.Linear.HyperbolicRealSplitting.LinearPowCommutes
import HolomorphicAnosov.Linear.HyperbolicRealSplitting.InversePowCancel
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Invariant stable and unstable subspaces of a hyperbolic real automorphism, commuting projections,
and exponential estimates in the given norm. Bounded integer orbits vanish. (Alves, Prop. 3.2 and
Thm 5.5)
-/

namespace HolomorphicAnosov

open Filter Topology _root_.Topology

/-- A hyperbolic automorphism of `Fin n → ℝ` admits complementary invariant subspaces and commuting
continuous projections, with exponential bounds for forward stable and inverse unstable
iterates. Every bounded integer orbit is zero. (Alves, Prop. 3.2 and Thm 5.5) -/
theorem hyperbolic_real_splitting
    (n : ℕ) (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hA : ∀ μ : ℂ, Module.End.HasEigenvalue (A.toLinearMap.baseChange ℂ) μ →
      ‖μ‖ ≠ 1) :
    ∃ (Es Eu : Submodule ℝ (Fin n → ℝ))
      (Ps Pu : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
      (Cs Cu rs ru : ℝ),
      IsCompl Es Eu ∧
      (∀ v ∈ Es, A v ∈ Es) ∧ (∀ v ∈ Eu, A v ∈ Eu) ∧
      (∀ v ∈ Es, A.symm v ∈ Es) ∧ (∀ v ∈ Eu, A.symm v ∈ Eu) ∧
      LinearMap.range Ps.toLinearMap = Es ∧
      LinearMap.range Pu.toLinearMap = Eu ∧
      Ps.comp Ps = Ps ∧ Pu.comp Pu = Pu ∧
      Ps + Pu = ContinuousLinearMap.id ℝ (Fin n → ℝ) ∧
      (∀ v, Ps (A v) = A (Ps v)) ∧
      (∀ v, Pu (A v) = A (Pu v)) ∧
      1 ≤ Cs ∧ 1 ≤ Cu ∧ 0 < rs ∧ rs < 1 ∧ 0 < ru ∧ ru < 1 ∧
      (∀ (j : ℕ) (v : Fin n → ℝ), v ∈ Es →
        ‖(A ^ j) v‖ ≤ Cs * rs ^ j * ‖v‖) ∧
      (∀ (j : ℕ) (v : Fin n → ℝ), v ∈ Eu →
        ‖(A.symm ^ j) v‖ ≤ Cu * ru ^ j * ‖v‖) ∧
      (∀ v : Fin n → ℝ,
        (∃ B : ℝ, ∀ k : ℤ, ‖(A ^ k) v‖ ≤ B) →
        ∀ k : ℤ, (A ^ k) v = 0) := by
  classical
  
  
  let Ac := A.toContinuousLinearEquiv
  obtain ⟨S, U, hS, hU, hSU, _⟩ := hyperbolic_decay_space_complement Ac hA
  have hss : ∀ v ∈ S, Ac v ∈ S := fun v hv ↦
    (hS _).mpr (decay_invariant Ac Ac (Commute.refl _) v ((hS v).mp hv))
  have hsu : ∀ v ∈ S, Ac.symm v ∈ S := fun v hv ↦
    (hS _).mpr (decay_invariant Ac Ac.symm (by
      change Ac * Ac.symm = Ac.symm * Ac
      apply ContinuousLinearEquiv.ext; funext w
      change Ac (Ac.symm w) = Ac.symm (Ac w)
      simp) v
      ((hS v).mp hv))
  have huu : ∀ v ∈ U, Ac.symm v ∈ U := fun v hv ↦
    (hU _).mpr (decay_invariant Ac.symm Ac.symm (Commute.refl _) v ((hU v).mp hv))
  have hus : ∀ v ∈ U, Ac v ∈ U := fun v hv ↦
    (hU _).mpr (decay_invariant Ac.symm Ac (by
      change Ac.symm * Ac = Ac * Ac.symm
      apply ContinuousLinearEquiv.ext; funext w
      change Ac.symm (Ac w) = Ac (Ac.symm w)
      simp) v
      ((hU v).mp hv))
  obtain ⟨Cs, rs, hCs, hrs, hrs1, hsbound⟩ :=
    restricted_exponential Ac S hss (fun v hv ↦ (hS v).mp hv)
  obtain ⟨Cu, ru, hCu, hru, hru1, hubound⟩ :=
    restricted_exponential Ac.symm U huu (fun v hv ↦ (hU v).mp hv)
  let Ps := (S.projection U hSU).toContinuousLinearMap
  let Pu := (U.projection S hSU.symm).toContinuousLinearMap
  have hPs : ∀ v, Ps (Ac v) = Ac (Ps v) := LatticeDensityPreparation.projection_commutes S U hSU Ac.toLinearMap hss hus
  have hPu : ∀ v, Pu (Ac v) = Ac (Pu v) := LatticeDensityPreparation.projection_commutes U S hSU.symm Ac.toLinearMap hus hss
  refine ⟨S, U, Ps, Pu, Cs, Cu, rs, ru, hSU, hss, hus, hsu, huu, ?_, ?_, ?_, ?_, ?_,
    hPs, hPu, hCs, hCu, hrs, hrs1, hru, hru1, ?_, ?_, ?_⟩
  · exact Submodule.range_projection hSU
  · exact Submodule.range_projection hSU.symm
  · apply ContinuousLinearMap.ext; intro v
    exact Submodule.projection_apply_of_mem_left hSU (Submodule.projection_apply_mem hSU v)
  · apply ContinuousLinearMap.ext; intro v
    exact Submodule.projection_apply_of_mem_left hSU.symm
      (Submodule.projection_apply_mem hSU.symm v)
  · apply ContinuousLinearMap.ext; intro v
    exact Submodule.projection_add_projection_eq_self hSU v
  · intro j v hv
    convert hsbound j v hv using 1
    congr 1
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ', pow_succ']; exact congrArg A ih
  · intro j v hv
    convert hubound j v hv using 1
    congr 1
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ', pow_succ']; exact congrArg A.symm ih
  · intro v hB k
    obtain ⟨B, hB⟩ := hB
    have hB0 : 0 ≤ B := (norm_nonneg v).trans (by simpa using hB 0)
    have hPnat := linear_pow_commutes A Ps hPs
    have hQnat := linear_pow_commutes A.symm Pu
      (LatticeDensityPreparation.projection_commutes U S hSU.symm Ac.symm.toLinearMap huu hsu)
    have hsb : ∀ j v, v ∈ S → ‖(A ^ j) v‖ ≤ Cs * rs ^ j * ‖v‖ := by
      intro j w hw
      convert hsbound j w hw using 1
      congr 1
      induction j with
      | zero => rfl
      | succ j ih => rw [pow_succ', pow_succ']; exact congrArg A ih
    have hub : ∀ j v, v ∈ U → ‖(A.symm ^ j) v‖ ≤ Cu * ru ^ j * ‖v‖ := by
      intro j w hw
      convert hubound j w hw using 1
      congr 1
      induction j with
      | zero => rfl
      | succ j ih => rw [pow_succ', pow_succ']; exact congrArg A.symm ih
    have hpbound : ∀ m : ℕ, ‖Ps v‖ ≤ (Cs * (‖Ps‖ * B)) * rs ^ m := by
      intro m
      have hcancel : Ps v = (A ^ m) (Ps ((A.symm ^ m) v)) := by
        rw [← hPnat, inverse_pow_cancel]
      rw [hcancel]
      refine (hsb m _ (Submodule.projection_apply_mem hSU _)).trans ?_
      have hb : ‖(A.symm ^ m) v‖ ≤ B := by
        change ‖((A⁻¹) ^ m) v‖ ≤ B
        simpa only [zpow_neg, zpow_natCast, ← inv_pow] using hB (-(m : ℤ))
      calc
        Cs * rs ^ m * ‖Ps ((A.symm ^ m) v)‖
            ≤ Cs * rs ^ m * (‖Ps‖ * B) := by
              gcongr; exact (Ps.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
        _ = (Cs * (‖Ps‖ * B)) * rs ^ m := by ring
    have hqbound : ∀ m : ℕ, ‖Pu v‖ ≤ (Cu * (‖Pu‖ * B)) * ru ^ m := by
      intro m
      have hcancel : Pu v = (A.symm ^ m) (Pu ((A ^ m) v)) := by
        rw [← hQnat]
        simpa only [LinearEquiv.symm_symm] using
          congrArg Pu (inverse_pow_cancel A.symm m v).symm
      rw [hcancel]
      refine (hub m _ (Submodule.projection_apply_mem hSU.symm _)).trans ?_
      have hb : ‖(A ^ m) v‖ ≤ B := by simpa only [zpow_natCast] using hB (m : ℤ)
      calc
        Cu * ru ^ m * ‖Pu ((A ^ m) v)‖ ≤ Cu * ru ^ m * (‖Pu‖ * B) := by
          gcongr; exact (Pu.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
        _ = (Cu * (‖Pu‖ * B)) * ru ^ m := by ring
    have hpzero : Ps v = 0 := norm_eq_zero.mp (le_antisymm
      (ge_of_tendsto (by simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hrs.le hrs1).const_mul (Cs * (‖Ps‖ * B)))
        (Filter.Eventually.of_forall hpbound)) (norm_nonneg _))
    have hqzero : Pu v = 0 := norm_eq_zero.mp (le_antisymm
      (ge_of_tendsto (by simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hru.le hru1).const_mul (Cu * (‖Pu‖ * B)))
        (Filter.Eventually.of_forall hqbound)) (norm_nonneg _))
    have hv : v = 0 := by
      have hsum := Submodule.projection_add_projection_eq_self hSU v
      change Ps v + Pu v = v at hsum
      simpa only [hpzero, hqzero, add_zero] using hsum.symm
    simp [hv]


end HolomorphicAnosov
