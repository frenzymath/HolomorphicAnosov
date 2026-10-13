import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.PolarDiskMap
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.AppendEuclidean

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

theorem polarDiskMap_fiber (m : ℕ) (x y : EuclideanSpace ℝ (Fin m))
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    polarDiskMap m x = polarDiskMap m y ↔ x = y ∨ ‖x‖ = 1 ∧ ‖y‖ = 1 := by
  constructor
  · intro h
    have hc : Real.cos (Real.pi * ‖x‖) = Real.cos (Real.pi * ‖y‖) := by
      simpa [polarDiskMap, appendEuclidean] using
        congrArg (fun z : EuclideanSpace ℝ (Fin (m + 1)) ↦ z (Fin.last m)) h
    have hr : ‖x‖ = ‖y‖ := by
      have hp := Real.injOn_cos ⟨mul_nonneg Real.pi_pos.le (norm_nonneg x), by nlinarith [Real.pi_pos]⟩
        ⟨mul_nonneg Real.pi_pos.le (norm_nonneg y), by nlinarith [Real.pi_pos]⟩ hc
      exact (mul_left_cancel₀ Real.pi_ne_zero hp)
    by_cases hb : ‖x‖ = 1
    · exact Or.inr ⟨hb, hr.symm.trans hb⟩
    · left
      by_cases hz : x = 0
      · have hyz : y = 0 := norm_eq_zero.mp (hr.symm.trans (by simp [hz]))
        exact hz.trans hyz.symm
      · have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hz
        have hsin : 0 < Real.sin (Real.pi * ‖x‖) :=
          Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hrpos)
            (by nlinarith [Real.pi_pos, lt_of_le_of_ne hx hb])
        have ha : Real.pi * Real.sinc (Real.pi * ‖x‖) ≠ 0 := by
          rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hrpos.ne')]
          exact mul_ne_zero Real.pi_ne_zero (div_ne_zero hsin.ne' (mul_ne_zero Real.pi_ne_zero hrpos.ne'))
        ext i
        have hh := congrArg (fun z : EuclideanSpace ℝ (Fin (m + 1)) ↦ z i.castSucc) h
        simp only [polarDiskMap, appendEuclidean, PiLp.toLp_apply, Fin.snoc_castSucc,
          PiLp.smul_apply, smul_eq_mul, ← hr] at hh
        exact mul_left_cancel₀ ha hh
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · simp [polarDiskMap, hx, hy, Real.sinc_of_ne_zero Real.pi_ne_zero, appendEuclidean]

end HolomorphicAnosov.Topology.Homology
