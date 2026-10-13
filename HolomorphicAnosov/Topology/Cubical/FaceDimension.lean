import HolomorphicAnosov.Topology.Cubical.ClosedCoordinateCell

/-!
# Dimension of a coordinate face

Source: Hatcher, *Algebraic Topology*, Appendix A.2, p.521, specialized to the
coordinate faces of the cubical-neighborhood construction.
-/

namespace HolomorphicAnosov.Cubical.ClosedCoordinateCell

/-- A coordinate face has dimension at most the dimension of its parent cell.
Every nondegenerate coordinate of the face must retain the whole parent interval:
either endpoint choice is degenerate. Thus its set of nondegenerate coordinates
is a subset of that of the parent, and finite cardinality is monotone.
Source: the dimension condition in Hatcher Appendix A.2, p.521. -/
theorem IsFace.dimension_le {N : ℕ} {a b : ClosedCoordinateCell N} (h : IsFace a b) :
    a.dimension ≤ b.dimension := by
  apply Set.ncard_mono
  intro i hi
  rcases h i with hfull | hlow | hupp
  · change a.lower i < a.upper i at hi
    rw [hfull.1, hfull.2] at hi
    exact hi
  · change a.lower i < a.upper i at hi
    rw [hlow.1, hlow.2] at hi
    exact False.elim (lt_irrefl _ hi)
  · change a.lower i < a.upper i at hi
    rw [hupp.1, hupp.2] at hi
    exact False.elim (lt_irrefl _ hi)


end HolomorphicAnosov.Cubical.ClosedCoordinateCell
