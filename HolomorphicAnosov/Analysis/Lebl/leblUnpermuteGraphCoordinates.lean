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

/-- Reassemble the first `n` coordinates and the last coordinate, then undo `σ`.

Source: Lebl version 3.4, Theorem 1.6.2, p. 36, reordering variables to solve for the last one.
Thus the reordered coordinates of this vector are exactly `Fin.snoc y w`.
-/
def leblUnpermuteGraphCoordinates {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (y : Fin n → ℂ) (w : ℂ) : Fin (n + 1) → ℂ :=
  fun i ↦ Fin.snoc (α := fun _ ↦ ℂ) y w (σ.symm i)

end HolomorphicAnosov.Analysis
