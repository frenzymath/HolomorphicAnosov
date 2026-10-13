import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Convexity
namespace HolomorphicAnosov.Topology

/-- A point of the standard interval outside its positive-coordinate interior
is one of its two vertices. Source: Hatcher, Algebraic Topology, ordered
simplex boundary p.103, used on the distinguished edge in Theorem 2A.1 p.167.
One nonnegative barycentric coordinate must vanish; since the two coordinates
sum to one, the other is one. The interval coordinate identifies the point
with the corresponding endpoint. -/
theorem stdSimplexOne_boundary_endpoints (t : StdSimplex ℝ (Fin 2))
    (ht : ¬ ∀ j, 0 < t.weights j) :
    t = StdSimplex.single 0 ∨ t = StdSimplex.single 1 := by
  push Not at ht
  obtain ⟨j, hj⟩ := ht
  have hsum := t.total_fin_two
  have h0 : (0 : ℝ) ≤ t.weights 0 := t.nonneg 0
  have h1 : (0 : ℝ) ≤ t.weights 1 := t.nonneg 1
  fin_cases j
  · change t.weights 0 ≤ 0 at hj
    right
    apply StdSimplex.homeomorphI.injective
    apply Subtype.ext
    change t.weights 1 = (StdSimplex.homeomorphI (StdSimplex.single 1)).val
    rw [StdSimplex.homeomorphI_single_one]
    change t.weights 1 = 1
    linarith
  · change t.weights 1 ≤ 0 at hj
    left
    apply StdSimplex.homeomorphI.injective
    apply Subtype.ext
    change t.weights 1 = (StdSimplex.homeomorphI (StdSimplex.single 0)).val
    rw [StdSimplex.homeomorphI_single_zero]
    change t.weights 1 = 0
    linarith

end HolomorphicAnosov.Topology
