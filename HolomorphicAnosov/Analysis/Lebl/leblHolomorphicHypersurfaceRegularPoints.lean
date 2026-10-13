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
import HolomorphicAnosov.Analysis.Lebl.leblHolomorphicZeroSet
import HolomorphicAnosov.Analysis.Lebl.leblHolomorphicZeroSetGraphAt

namespace HolomorphicAnosov.Analysis

open Set
open scoped ContDiff

/-- Regular graph points as a subset of the zero set with its intrinsic subtype topology.

Source: Lebl version 3.4, Theorem 1.6.2, p. 36. Openness and density below are in this subtype,
not in the ambient coordinate space. The set is empty when the zero set is empty.
-/
def leblHolomorphicHypersurfaceRegularPoints {n : ℕ} (U : Set (Fin (n + 1) → ℂ))
    (a : (Fin (n + 1) → ℂ) → ℂ) : Set (leblHolomorphicZeroSet U a) :=
  {p | leblHolomorphicZeroSetGraphAt U a p.1}

end HolomorphicAnosov.Analysis
