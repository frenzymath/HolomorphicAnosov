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

/-- The underlying zero set in its specified open domain.

Source: Lebl version 3.4, Theorem 1.6.2, p. 36: `N` is the inverse image of zero in `U`.
Values of the totalized defining function outside `U` do not belong to this set.
-/
def leblHolomorphicZeroSet {n : ℕ} (U : Set (Fin (n + 1) → ℂ))
    (a : (Fin (n + 1) → ℂ) → ℂ) : Set (Fin (n + 1) → ℂ) :=
  {z | z ∈ U ∧ a z = 0}

end HolomorphicAnosov.Analysis
