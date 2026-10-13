import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.Definitions

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

theorem integralToralMap_continuous {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ) : Continuous (integralToralMap A) := by
  exact continuous_pi fun i ↦ continuous_finsetSum _ fun j _ ↦
    (continuous_apply j).zsmul (A i j)


end
end HolomorphicAnosov.Dynamics
