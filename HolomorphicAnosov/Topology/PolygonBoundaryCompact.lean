import Mathlib.Geometry.Polygon.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.Compactness.Compact

/-!
# Compactness of a finite polygon boundary

Source: Munkres, *Topology*, second edition (2000), Theorem 26.5, p.166,
continuous images of compact spaces; Lee, *Introduction to Topological
Manifolds*, second edition (2011), Theorem 5.14, p.137, first paragraph of the proof,
the finite union of compact cell closures. Here the individual closed cells
are the affine images of the compact real interval `[0,1]`. No cell-complex
structure, simplicity, or nondegeneracy is needed for this finite-union argument.
-/

namespace Polygon

/-- The boundary of any finite polygon in a real normed space is compact.

Each edge is the continuous affine image of `[0,1]`, hence compact by
Munkres Theorem 26.5. The boundary is the finite union of those compact edges,
using the finite-union argument written in Lee Theorem 5.14. The empty polygon
and polygons with repeated vertices or zero-length edges are included. -/
theorem isCompact_boundary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (p : Polygon E n) : IsCompact (p.boundary ℝ) := by
  apply isCompact_iUnion
  intro i
  rw [edgeSet_eq_image_edgePath (R := ℝ)]
  exact isCompact_Icc.image (by dsimp [edgePath]; fun_prop)

end Polygon

