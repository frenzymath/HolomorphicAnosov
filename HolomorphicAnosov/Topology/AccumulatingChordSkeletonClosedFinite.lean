import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Convex.Segment

namespace HolomorphicAnosov
open Set

/--
For a finite attached-chord family, the chord skeleton is closed by finite
closed-union reasoning. This is the finite-family branch of Cairns' attached
chord compactness argument; the countable null-family branch is kept in the
parent provider.
-/
theorem accumulatingChordSkeleton_closed_of_finite
    {ι : Type*} [Finite ι]
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (_arcs : ι → Set Circle) (u v : ι → Circle) :
    IsClosed (Set.range σ ∪ ⋃ i, segment ℝ (σ (u i)) (σ (v i))) := by
  have hbase : IsClosed (Set.range σ) :=
    (isCompact_range hσ.continuous).isClosed
  have hchord (i : ι) : IsClosed (segment ℝ (σ (u i)) (σ (v i))) := by
    rw [segment_eq_image_lineMap]
    apply (isCompact_Icc.image ?_).isClosed
    change Continuous (fun t : ℝ => t • (σ (v i) - σ (u i)) + σ (u i))
    exact (continuous_id.smul continuous_const).add continuous_const
  exact hbase.union (isClosed_iUnion_of_finite hchord)


end HolomorphicAnosov
