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

theorem integralToralMap_one {n : ℕ} (x : UnitAddTorus (Fin n)) :
    integralToralMap (1 : Matrix.GeneralLinearGroup (Fin n) ℤ) x = x := by
  ext i
  simp [integralToralMap, Matrix.one_apply]

end
end HolomorphicAnosov.Dynamics
