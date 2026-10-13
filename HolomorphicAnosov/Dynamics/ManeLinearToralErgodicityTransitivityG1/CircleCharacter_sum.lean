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

theorem circleCharacter_sum {ι : Type*} (s : Finset ι) (x : ι → UnitAddCircle) :
    (AddCircle.toCircle (∑ i ∈ s, x i) : ℂ) =
      ∏ i ∈ s, (AddCircle.toCircle (x i) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, Finset.prod_insert ha, AddCircle.toCircle_add,
      Circle.coe_mul, ih]

end
end HolomorphicAnosov.Dynamics
