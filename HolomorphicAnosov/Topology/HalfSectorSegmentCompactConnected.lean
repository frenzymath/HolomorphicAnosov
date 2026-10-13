import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.PathConnected

namespace HolomorphicAnosov

open Set

/-- The closed affine segment used in Cairns's Case I front is compact and connected.
This is the elementary compact-parametrization step behind Cairns §3(C2), pp.862–863:
the segment is the continuous image of the compact interval and is convex, hence
connected. The statement remains valid for coincident endpoints (the parent guards
nondegeneracy separately). -/
theorem halfSector_segment_compact_connected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) :
    IsCompact (segment ℝ x y) ∧ IsConnected (segment ℝ x y) := by
  constructor
  · rw [segment_eq_image_lineMap]
    have hcont : Continuous (AffineMap.lineMap x y : ℝ → E) := by
      rw [show (AffineMap.lineMap x y : ℝ → E) = (fun t : ℝ ↦ (1 - t) • x + t • y) by
        funext t
        simp [AffineMap.lineMap_apply]
        module]
      fun_prop
    exact isCompact_Icc.image hcont
  · exact (convex_segment (𝕜 := ℝ) x y).isConnected
      ⟨x, left_mem_segment ℝ x y⟩

end HolomorphicAnosov
