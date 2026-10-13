import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Segment

namespace HolomorphicAnosov

open Set
open Filter
open scoped Topology _root_.Topology

/--
A recurring chord in the attached-chord skeleton contributes no new limit
point.  This is the recurring-index branch of the sequence argument in
Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem*, §3(E)--§4(A),
pp.863--864: a fixed chord is the continuous affine image of the compact
interval `Icc 0 1`, hence is closed in `ℂ`, and a convergent sequence lying on
that chord has its limit on the chord.
-/
theorem accumulatingChordSkeleton_recurring_index_limit
    (a b : ℂ) (x : ℕ → ℂ) (z : ℂ)
    (hx : ∀ n, x n ∈ segment ℝ a b)
    (hz : Tendsto x atTop (𝓝 z)) :
    z ∈ segment ℝ a b := by
  have hclosed : IsClosed (segment ℝ a b) := by
    rw [segment_eq_image_lineMap]
    apply (isCompact_Icc.image ?_).isClosed
    change Continuous (fun t : ℝ => t • (b - a) + a)
    exact (continuous_id.smul continuous_const).add continuous_const
  exact hclosed.mem_of_tendsto hz (Eventually.of_forall hx)


end HolomorphicAnosov
