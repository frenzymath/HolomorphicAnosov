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

/-- The period-one product normalized Haar probability measure on the canonical real torus.

Source: Mañé I§7, p. 47, normalized Haar measure, and II§3, pp. 106–108, the torus measure.
Mathlib's `AddCircle.haarAddCircle` is Haar measure with total mass one; `Measure.pi` is the
finite product. The period is explicitly one. In dimension zero the empty product is the unit
point mass on the singleton empty-coordinate torus, not a zero measure. The data in this
definition contain no postponed proof or choice of a different normalization.
-/
noncomputable def maneUnitTorusHaar (n : ℕ) : Measure (UnitAddTorus (Fin n)) :=
  Measure.pi fun _ : Fin n ↦ @AddCircle.haarAddCircle (1 : ℝ) ⟨zero_lt_one⟩


noncomputable def integralToralAddHom {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    UnitAddTorus (Fin n) →+ UnitAddTorus (Fin n) where
  toFun := integralToralMap A
  map_zero' := by ext i; simp [integralToralMap]
  map_add' x y := by ext i; simp [integralToralMap, smul_add, Finset.sum_add_distrib]

instance maneHaar_isAddHaar (n : ℕ) : (maneUnitTorusHaar n).IsAddHaarMeasure := by
  unfold maneUnitTorusHaar
  infer_instance

instance maneHaar_isProbability (n : ℕ) : IsProbabilityMeasure (maneUnitTorusHaar n) := by
  unfold maneUnitTorusHaar
  infer_instance


end
end HolomorphicAnosov.Dynamics
