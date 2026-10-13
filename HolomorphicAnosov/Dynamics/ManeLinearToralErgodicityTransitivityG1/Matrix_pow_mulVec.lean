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

theorem matrix_pow_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (r : ℕ) (k : Fin n → ℤ) : (M ^ r).mulVec k = M.mulVec^[r] k := by
  induction r generalizing k with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, ih, Function.iterate_succ_apply]

end
end HolomorphicAnosov.Dynamics
