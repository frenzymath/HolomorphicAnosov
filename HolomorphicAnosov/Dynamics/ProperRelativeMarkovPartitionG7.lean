import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Proper Markov partitions relative to an invariant set

Source: Rufus Bowen, *Markov Partitions for Axiom A Diffeomorphisms*,
Amer. J. Math. 92 (1970), pp. 725--747: closed orbit plaques and Fact 1,
pp. 726--727; the rectangle definition, p. 729; rectangle partitions and
the two Markov inclusions, p. 731. The ambient map remains the original
homeomorphism. Every rectangle and interior below is relative to the actual
invariant subset, with its inherited metric and topology.
-/

namespace HolomorphicAnosov.Dynamics

variable {X : Type*} [MetricSpace X]

/-- Bowen's closed local stable plaque, defined by all forward orbit distances
in the specified metric, including time zero (printed p. 726). -/
def relativeClosedStablePlaque (f : X ≃ₜ X) (γ : ℝ) (x : X) : Set X :=
  {y | ∀ n : ℕ, dist ((f : X → X)^[n] y) ((f : X → X)^[n] x) ≤ γ}

/-- Bowen's closed local unstable plaque, defined by all inverse orbit distances
in the specified metric, including time zero (printed p. 726). -/
def relativeClosedUnstablePlaque (f : X ≃ₜ X) (γ : ℝ) (x : X) : Set X :=
  {y | ∀ n : ℕ, dist ((f.symm : X → X)^[n] y) ((f.symm : X → X)^[n] x) ≤ γ}

/-- A finite proper small Markov partition of a nonempty compact invariant subset
for the original map, with Bowen's stable-first bracket convention.

Source: Bowen (1970), pp. 726--727, 729 and 731. The stored homeomorphism `onSet`
is the actual restriction of `f`: its inclusion into the ambient space agrees
pointwise with `f`. Thus forward and inverse iterates in both plaques are those
of the original restricted dynamics, not a replacement map. Rectangles are
subsets of the literal subtype `Λ`; all closure, interior and disjointness laws
use its inherited topology. No manifold structure on `Λ`, connected rectangle,
ambient-space cover, or differentiable conjugacy is specified.

The close-pair bracket is represented by a total function, whose membership,
uniqueness and continuity are required only where `dist x y ≤ ε`. The rectangle
diameter bound uses a scale at most `ε`, so every rectangle bracket is on that
domain. Values outside that domain are unconstrained and never enter a defining
law. Compactness of `Λ` and closedness of its rectangles make their real metric
diameters the usual finite diameters. Properness is literal regular closure
and disjoint relative interiors. Both `x ∈ interior Rᵢ` and
`onSet x ∈ interior Rⱼ` are required before either Markov inclusion. The unstable
image contains the target unstable slice; the stable image is contained in the
target stable slice. The definition contains no postponed proof or claim of
existence of such a partition.
-/
structure ProperRelativeMarkovPartition {M : Type*} [MetricSpace M]
    (f : M ≃ₜ M) (Λ : Set M) where
  nonempty : Λ.Nonempty
  compact : IsCompact Λ
  onSet : Λ ≃ₜ Λ
  onSet_eq : ∀ x : Λ, (onSet x).val = f x.val
  γ : ℝ
  γ_pos : 0 < γ
  ε : ℝ
  ε_pos : 0 < ε
  bracket : Λ → Λ → Λ
  bracket_mem : ∀ x y : Λ, dist x y ≤ ε →
    bracket x y ∈ relativeClosedStablePlaque onSet γ x ∩
      relativeClosedUnstablePlaque onSet γ y
  bracket_unique : ∀ x y : Λ, dist x y ≤ ε → ∀ z : Λ,
    z ∈ relativeClosedStablePlaque onSet γ x ∩ relativeClosedUnstablePlaque onSet γ y →
      z = bracket x y
  bracket_continuous : ContinuousOn (fun p : Λ × Λ ↦ bracket p.1 p.2)
    {p | dist p.1 p.2 ≤ ε}
  rectangleScale : ℝ
  rectangleScale_pos : 0 < rectangleScale
  rectangleScale_le_close : rectangleScale ≤ ε
  N : ℕ
  rectangles : Fin N → Set Λ
  rectangles_nonempty : ∀ i, (rectangles i).Nonempty
  rectangles_closed : ∀ i, IsClosed (rectangles i)
  rectangles_regularClosed : ∀ i, closure (interior (rectangles i)) = rectangles i
  rectangles_small : ∀ i, Metric.diam (rectangles i) ≤ rectangleScale
  rectangles_bracket : ∀ i, ∀ x ∈ rectangles i, ∀ y ∈ rectangles i,
    bracket x y ∈ rectangles i
  cover : ∀ x : Λ, ∃ i, x ∈ rectangles i
  disjoint_interiors : ∀ i j : Fin N, i ≠ j →
    Disjoint (interior (rectangles i)) (interior (rectangles j))
  stable_markov : ∀ (i j : Fin N) (x : Λ),
    x ∈ interior (rectangles i) → onSet x ∈ interior (rectangles j) →
      onSet '' (rectangles i ∩ relativeClosedStablePlaque onSet γ x) ⊆
        rectangles j ∩ relativeClosedStablePlaque onSet γ (onSet x)
  unstable_markov : ∀ (i j : Fin N) (x : Λ),
    x ∈ interior (rectangles i) → onSet x ∈ interior (rectangles j) →
      rectangles j ∩ relativeClosedUnstablePlaque onSet γ (onSet x) ⊆
        onSet '' (rectangles i ∩ relativeClosedUnstablePlaque onSet γ x)

end HolomorphicAnosov.Dynamics
