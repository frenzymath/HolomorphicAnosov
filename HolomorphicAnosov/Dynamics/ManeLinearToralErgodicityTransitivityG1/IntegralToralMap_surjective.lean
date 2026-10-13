import HolomorphicAnosov.Topology.IntegralToralMapComp
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.Definitions
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.IntegralToralMap_one

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

theorem integralToralMap_surjective {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ) : Function.Surjective (integralToralMap A) := by
  intro x
  refine ⟨integralToralMap A⁻¹ x, ?_⟩
  rw [HolomorphicAnosov.integral_toral_map_comp, mul_inv_cancel, integralToralMap_one]


end
end HolomorphicAnosov.Dynamics
