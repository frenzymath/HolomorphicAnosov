import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import Mathlib.Topology.ContinuousMap.Algebra

/-! The canonical continuous integral toral map used by Franks's construction.
Source: Franks (1970), pp. 62–63 and 70. -/

namespace HolomorphicAnosov

open _root_.Topology

/-- The existing integral row action, bundled using the continuous-map finite-sum operations.

Source: Franks, pp. 62–63 and 70, the integral linear map descending to the torus.
Each coordinate is the sum of the integer multiples of the coordinate projections.
The underlying function is exactly `integralToralMap A`; this supplies its topology, not a
second action or an abstract chosen toral automorphism. Dimension zero uses the empty sum.
-/
noncomputable def franksIntegralToralContinuousMap {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
  ContinuousMap.pi fun i ↦ ∑ j : Fin n, A i j • ContinuousMap.eval j

end HolomorphicAnosov
