import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.Definitions
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.IntegralToralMap_continuous
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.IntegralToralMap_surjective

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

theorem integralToralMap_measurePreserving {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    MeasurePreserving (integralToralMap A) (maneUnitTorusHaar n) (maneUnitTorusHaar n) :=
  (integralToralAddHom A).measurePreserving (integralToralMap_continuous A)
    (integralToralMap_surjective A) rfl

-- Mañé Lemma 3.3(b), on the literal integer row action.

end
end HolomorphicAnosov.Dynamics
