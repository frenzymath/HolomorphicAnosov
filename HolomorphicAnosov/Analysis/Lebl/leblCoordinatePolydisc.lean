import HolomorphicAnosov.Analysis.Complex.LeblPolydiscCoordinateDerivatives
import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.Connected.Basic

namespace HolomorphicAnosov.Analysis

open Set
open scoped ContDiff

/-- The open coordinate polydisc with center `c` and coordinate radii `r`.

Source: Lebl version 3.4, §1.1 Definition 1.1.1, p. 11, and §1.6 Theorem 1.6.2, p. 36.
Its graph witnesses
require every radius to be strictly positive. For zero coordinates this is the singleton
zero-dimensional complex space, since the coordinate condition is vacuous.
-/
def leblCoordinatePolydisc {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) :
    Set (Fin n → ℂ) :=
  {z | ∀ i, ‖z i - c i‖ < r i}

end HolomorphicAnosov.Analysis
