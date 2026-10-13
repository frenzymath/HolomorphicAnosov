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
import HolomorphicAnosov.Analysis.Lebl.leblUnpermuteGraphCoordinates
import HolomorphicAnosov.Analysis.Lebl.leblHolomorphicZeroSet

namespace HolomorphicAnosov.Analysis

open Set
open scoped ContDiff

/-- A zero-set point with a local holomorphic hypersurface graph after permuting coordinates.

Source: Lebl version 3.4, Theorem 1.6.2 and the definition immediately following its proof,
p. 36. Positive-radius polydiscs give a product neighborhood of `p` inside `U`. The graph
function is holomorphic on the parameter polydisc, has values in the last-coordinate disk,
and the displayed iff identifies every zero in that product with precisely its graph.
No assertion about the gradient of the original defining function is made.
-/
def leblHolomorphicZeroSetGraphAt {n : ℕ} (U : Set (Fin (n + 1) → ℂ))
    (a : (Fin (n + 1) → ℂ) → ℂ) (p : Fin (n + 1) → ℂ) : Prop :=
  p ∈ leblHolomorphicZeroSet U a ∧
    ∃ (σ : Equiv.Perm (Fin (n + 1))) (c : Fin n → ℂ) (r : Fin n → ℝ)
      (d : ℂ) (s : ℝ) (g : (Fin n → ℂ) → ℂ),
      (∀ i, 0 < r i) ∧ 0 < s ∧
      (fun i ↦ p (σ i.castSucc)) ∈ leblCoordinatePolydisc c r ∧
      ‖p (σ (Fin.last n)) - d‖ < s ∧
      DifferentiableOn ℂ g (leblCoordinatePolydisc c r) ∧
      MapsTo g (leblCoordinatePolydisc c r) (Metric.ball d s) ∧
      (∀ y ∈ leblCoordinatePolydisc c r, ∀ w ∈ Metric.ball d s,
        leblUnpermuteGraphCoordinates σ y w ∈ U) ∧
      (∀ y ∈ leblCoordinatePolydisc c r, ∀ w ∈ Metric.ball d s,
        a (leblUnpermuteGraphCoordinates σ y w) = 0 ↔ w = g y)

end HolomorphicAnosov.Analysis
