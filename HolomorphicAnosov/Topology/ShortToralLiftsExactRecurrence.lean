import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import HolomorphicAnosov.Topology.IntegralToralMapRealLift
import HolomorphicAnosov.Topology.ShortIntegerLatticeVectorZero
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

namespace HolomorphicAnosov

/-- Two short consecutive real representatives of an actual toral orbit satisfy
exact real matrix recurrence, since their discrepancy is an integer vector of
norm less than one. Source: Manning Lemma 6, pp.427–428, target canonical-coordinate
argument. The finite-product norm and original row-matrix action are kept literally. -/
theorem short_toral_lifts_exact_recurrence
    {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (v w : Fin n → ℝ) (a : ℝ) (hv : ‖v‖ ≤ a) (hw : ‖w‖ ≤ a)
    (hquot : (fun i ↦ (w i : UnitAddCircle)) =
      integralToralMap A (fun i ↦ (v i : UnitAddCircle))) :
    let T := (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℝ))).toContinuousLinearMap
    (‖T‖ + 1) * a < 1 → w = T v := by
  dsimp only
  let T := (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℝ))).toContinuousLinearMap
  intro hsmall
  have hquot' := hquot.trans (integral_toral_map_real_lift A v)
  have hzero : ∀ i, ((w - T v) i : UnitAddCircle) = 0 := by
    intro i
    have hi := congrFun hquot' i
    change ((w i - (T v) i : ℝ) : UnitAddCircle) = 0
    rw [AddCircle.coe_sub]
    apply sub_eq_zero.mpr
    exact hi
  have hnorm : ‖w - T v‖ < 1 := by
    calc
      ‖w - T v‖ ≤ ‖w‖ + ‖T v‖ := norm_sub_le _ _
      _ ≤ a + ‖T‖ * a := add_le_add hw
        ((T.le_opNorm v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg T)))
      _ = (‖T‖ + 1) * a := by ring
      _ < 1 := hsmall
  exact sub_eq_zero.mp (short_integer_lattice_vector_zero (w - T v) hzero hnorm)

end HolomorphicAnosov
