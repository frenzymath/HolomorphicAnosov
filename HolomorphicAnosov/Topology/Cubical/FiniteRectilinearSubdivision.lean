import HolomorphicAnosov.Topology.Cubical.ClosedCoordinateCell

/-!
# Finite rectilinear cubical subdivisions in their original ambient coordinates

Source: Hatcher, *Algebraic Topology*, Appendix A.2, p. 521, and the coordinate-cell
realization in `topo.finite_cubical_skeleton_homology_neighborhoods_g7`, proof Q1.
-/

namespace HolomorphicAnosov.Cubical

open ClosedCoordinateCell

/-- A finite closed coordinate subdivision of a full-dimensional cube. All faces
are present, and every nonempty intersection is a common face, so overlapping
interiors and partial-face junctions are excluded. The cover is an equality of
literal subsets of the original `Fin N → ℝ`.
Source: Hatcher Appendix A.2, p. 521, coordinate-cell specialization in Q1. -/
structure FiniteRectilinearSubdivision (N : ℕ) where
  /-- The outer coordinate cube. -/
  cube : ClosedCoordinateCell N
  /-- The common side length is positive. -/
  cube_side : ∃ s : ℝ, 0 < s ∧ ∀ i, cube.upper i - cube.lower i = s
  /-- The actual closed coordinate cells, including all faces. -/
  cells : Set (ClosedCoordinateCell N)
  /-- The subdivision contains finitely many cells. -/
  finite_cells : cells.Finite
  /-- Every face belongs to the subdivision. -/
  faces : ∀ c ∈ cells, ∀ a, IsFace a c → a ∈ cells
  /-- Intersecting cells meet along a whole common face. -/
  intersections : ∀ a ∈ cells, ∀ b ∈ cells,
    (carrier a ∩ carrier b).Nonempty →
      ∃ d ∈ cells, IsFace d a ∧ IsFace d b ∧ carrier d = carrier a ∩ carrier b
  /-- The cells cover exactly the given outer cube. -/
  cover : (⋃ c ∈ cells, carrier c) = carrier cube

namespace FiniteRectilinearSubdivision

variable {N : ℕ}

/-- The q-skeleton is the literal union of cells of dimension at most q.
Source: Hatcher, Lemma 2.34, pp. 137–139, and Appendix A.2, p. 521. -/
def skeleton (K : FiniteRectilinearSubdivision N) (q : ℕ) : Set (Fin N → ℝ) :=
  ⋃ c ∈ K.cells, ⋃ (_ : c.dimension ≤ q), c.carrier

end FiniteRectilinearSubdivision

/-- A cubical subcomplex selects cells closed under taking all faces. Its cells
are a subset of the original subdivision's cells; no alternative topology or
characteristic maps are included. The empty cell family is allowed.
Source: Hatcher, Appendix, pp. 520–521, definition of a CW subcomplex, specialized
to the closed coordinate cells in Q1 of the cubical-neighborhood node. -/
structure CubicalSubcomplex {N : ℕ} (K : FiniteRectilinearSubdivision N) where
  /-- The selected original cells. -/
  cells : Set (ClosedCoordinateCell N)
  /-- Every selected cell is an original subdivision cell. -/
  subset_cells : cells ⊆ K.cells
  /-- Every face of a selected cell is selected. -/
  faces : ∀ c ∈ cells, ∀ a, IsFace a c → a ∈ cells

namespace CubicalSubcomplex

variable {N : ℕ} {K : FiniteRectilinearSubdivision N}

/-- The subcomplex carrier has its original embedded subset topology.
Source: Hatcher, Appendix, pp. 520–521, induced topology of a subcomplex. -/
def carrier (D : CubicalSubcomplex K) : Set (Fin N → ℝ) :=
  ⋃ c ∈ D.cells, c.carrier

/-- The q-skeleton of the selected original cells.
Source: Hatcher, Lemma 2.34, pp. 137–139. -/
def skeleton (D : CubicalSubcomplex K) (q : ℕ) : Set (Fin N → ℝ) :=
  ⋃ c ∈ D.cells, ⋃ (_ : c.dimension ≤ q), c.carrier

end CubicalSubcomplex

end HolomorphicAnosov.Cubical
