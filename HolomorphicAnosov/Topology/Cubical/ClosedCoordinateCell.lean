import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Closed coordinate cells, including their degenerate faces

Source: Hatcher, *Algebraic Topology*, Appendix A.2, p. 521, applied to coordinate
boxes and all their faces as in `topo.finite_cubical_skeleton_homology_neighborhoods_g7`,
proof Q1. The carrier is the literal closed interval in the coordinatewise order on
`Fin N → ℝ`. Equal endpoints are permitted, so vertices and lower-dimensional faces
remain embedded subsets of the original ambient space.
-/

namespace HolomorphicAnosov.Cubical

/-- A closed coordinate cell is given by two ordered corners. Equal coordinates give
the degenerate directions. Source: Hatcher Appendix A.2, p. 521, coordinate-box
characteristic-cell specialization in the cubical-neighborhood node, Q1. -/
structure ClosedCoordinateCell (N : ℕ) where
  /-- Lower corner in the original ambient coordinates. -/
  lower : Fin N → ℝ
  /-- Upper corner in the original ambient coordinates. -/
  upper : Fin N → ℝ
  /-- Every interval is nonempty, including degenerate intervals. -/
  lower_le_upper : lower ≤ upper

namespace ClosedCoordinateCell

variable {N : ℕ}

/-- The original embedded closed box. Source: Hatcher Appendix A.2, p. 521,
coordinate-cell realization used in Q1 of the cubical-neighborhood node. -/
def carrier (c : ClosedCoordinateCell N) : Set (Fin N → ℝ) :=
  Set.Icc c.lower c.upper

/-- Cell dimension is the number of nondegenerate coordinate directions.
Source: the coordinate-cell dimension in Hatcher Appendix A.2, p. 521. -/
noncomputable def dimension (c : ClosedCoordinateCell N) : ℕ :=
  {i : Fin N | c.lower i < c.upper i}.ncard

/-- A face is obtained independently in each coordinate by retaining the whole
interval or selecting either endpoint. The whole cell is also a face.
Source: Hatcher Appendix A.2, p. 521, boundaries as unions of proper faces in Q1. -/
def IsFace (a b : ClosedCoordinateCell N) : Prop :=
  ∀ i : Fin N,
    (a.lower i = b.lower i ∧ a.upper i = b.upper i) ∨
      (a.lower i = b.lower i ∧ a.upper i = b.lower i) ∨
      (a.lower i = b.upper i ∧ a.upper i = b.upper i)

end ClosedCoordinateCell

end HolomorphicAnosov.Cubical
