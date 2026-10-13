import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import HolomorphicAnosov.Topology.StandardCoordinateSimplexClosedConvexBounded
import HolomorphicAnosov.Topology.StandardCoordinateSimplexInteriorFrontier
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace HolomorphicAnosov

open Set Topology _root_.Topology Metric Bornology

/-!
# Geometric facts about the standard barycentric coordinate body

This is the body-level prerequisite for the radial characteristic map.  It is
kept separate so the characteristic-map theorem does not hide the finite
maximum-norm perturbation argument in an anonymous proof.
-/

/-- The normalized barycentric coordinate body is a closed bounded convex body,
with the expected strict-coordinate interior and barycentric frontier.

Source: Hatcher, *Algebraic Topology*, §2.1, pp.103–104, where a simplex is
identified with normalized nonnegative barycentric coordinates, and Proposition
A.2, p.521, for the closed-cell/interior/frontier decomposition.  The
finite-product norm calculations use the pinned Mathlib finite-Pi norm APIs.

Natural-language proof obligation: on `V = Fin d → ℝ`, let
`Delta = {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}` and
`I = {u | (∀ i, 0 < u i) ∧ ∑ i, u i < 1}`.  Each defining inequality is closed,
and convexity is preserved by affine interpolation.  Every coordinate of a
point in Delta is between zero and one, so the native maximum norm bounds Delta.
The point with all coordinates `1/(d+1)` is in I, including d=0.  A positive
minimum of finitely many coordinates and a strict sum margin produce a ball
inside Delta; conversely, subtracting in a zero coordinate or adding in one
coordinate at a sum-equality point leaves Delta, proving `interior Delta = I`.
Because Delta is closed, its frontier is Delta minus I.  Writing the first
barycentric coordinate as `1 - ∑u` and the remaining coordinates as `u i`
identifies that frontier with the normalized nonnegative families having a
zero coefficient, hence with proper barycentric faces; for d=0 both sides are
empty.  No nontriviality, ambient Euclidean norm, or nonempty-complex
hypothesis is used.
-/
theorem standard_coordinate_simplex_body (d : ℕ) :
    let V := Fin d → ℝ
    let Delta : Set V := {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}
    let I : Set V := {u | (∀ i, 0 < u i) ∧ ∑ i, u i < 1}
    Convex ℝ Delta ∧
      IsClosed Delta ∧
      IsBounded Delta ∧
      (interior Delta).Nonempty ∧
      interior Delta = I ∧
      frontier Delta = Delta \ I := by
  dsimp
  obtain ⟨hconv, hclosed, hbounded⟩ := standard_coordinate_simplex_closed_convex_bounded d
  obtain ⟨hneI, hinterior⟩ := standard_coordinate_simplex_interior d
  have hne : (interior ({u : Fin d → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1})).Nonempty := by
    rw [hinterior]
    exact hneI
  have hfrontier : frontier ({u : Fin d → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}) =
      ({u : Fin d → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}) \ {u : Fin d → ℝ | (∀ i, 0 < u i) ∧ ∑ i, u i < 1} := by
    rw [frontier, hclosed.closure_eq, hinterior]
  exact ⟨hconv, hclosed, hbounded, hne, hinterior, hfrontier⟩


end HolomorphicAnosov
