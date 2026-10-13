import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.Definitions
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.CircleCharacter_sum

import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Eigenspace.Matrix

namespace HolomorphicAnosov.Dynamics
open MeasureTheory
noncomputable section

theorem mFourier_integralToralMap {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ) (k : Fin n → ℤ)
    (x : UnitAddTorus (Fin n)) :
    UnitAddTorus.mFourier k (integralToralMap A x) =
      UnitAddTorus.mFourier (fun j ↦ ∑ i, A i j * k i) x := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, integralToralMap, fourier_apply]
  simp_rw [Finset.smul_sum, circleCharacter_sum, smul_smul]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j hj
  rw [← circleCharacter_sum, ← Finset.sum_smul]
  have hcoeff : (∑ i, k i * A i j) = ∑ i, A i j * k i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  rw [hcoeff]

end
end HolomorphicAnosov.Dynamics
