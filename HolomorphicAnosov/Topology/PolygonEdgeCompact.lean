import Mathlib.Geometry.Polygon.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Affine

namespace Polygon

/-- Each finite polygon edge is compact, as the affine image of `[0,1]`.
This supplies the closed-edge premise needed by finite intersection-graph arguments. -/
theorem isCompact_edgeSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (p : Polygon E n) (i : Fin n) : IsCompact (p.edgeSet ℝ i) := by
  rw [edgeSet_eq_image_edgePath (R := ℝ)]
  exact isCompact_Icc.image (by dsimp [edgePath]; fun_prop)

end Polygon
