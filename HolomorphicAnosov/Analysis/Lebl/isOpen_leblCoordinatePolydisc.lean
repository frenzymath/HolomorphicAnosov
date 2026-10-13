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
import HolomorphicAnosov.Analysis.Lebl.leblCoordinatePolydisc

namespace HolomorphicAnosov.Analysis

open Set
open scoped ContDiff

/-- Lebl, Tasty Bits of Several Complex Variables v3.4, §1.6 Theorem 1.6.2 p.36.
Public auxiliary result in the regular-hypersurface proof. -/
lemma isOpen_leblCoordinatePolydisc {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) :
    IsOpen (leblCoordinatePolydisc c r) := by
  simp only [leblCoordinatePolydisc, ofPred_forall]
  change IsOpen (⋂ i, {z : Fin n → ℂ | ‖z i - c i‖ < r i})
  exact isOpen_iInter_of_finite fun i ↦ isOpen_lt
    (((continuous_apply i).sub continuous_const).norm) continuous_const

end HolomorphicAnosov.Analysis
