import HolomorphicAnosov.Topology.AccumulatingChordEndpointDistance
import HolomorphicAnosov.Topology.AccumulatingChordArcClassification
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Convex.Segment

namespace HolomorphicAnosov
open Set Filter MeasureTheory
open scoped Topology _root_.Topology

/--
The distinct-index branch of the countable attached-chord closedness argument.
Cairns §3(E)--§4(A), pp.863--864, and de Carvalho Definition 4.3/Lemma 4.4,
pp.29--30, use normalized circle length to show that pairwise disjoint proper
source arcs form a null family.  More explicitly, lift each proper connected
open arc to a bounded real angular interval of length in (0, 2π). Its closure
has the stated endpoints. Normalized circle measure bounds the sum of the
lengths of any finite disjoint subfamily by one, so only finitely many arcs
can exceed each positive normalized length. Pairwise distinct selected arcs
therefore have lengths tending to zero. Their endpoint distances tend to zero
on the parameter circle, and uniform continuity of σ on compact Circle gives
dist (σ (u (i n))) (σ (v (i n))) tending to zero. Every point of the n-th
straight segment is at most that endpoint distance from σ (u (i n)). Since
x tends to z, these chosen endpoints also tend to z. The range of σ is compact
and therefore closed in ℂ, so z belongs to it. This proof includes major arcs
and arcs crossing an angular cut; finitely many such large arcs do not affect
the limit, and shared endpoints are allowed.
-/
theorem accumulatingChordSkeleton_distinct_index_limit
    {ι : Type*} [Countable ι] [Infinite ι]
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (_h : (Set.range σ) ≃ₜ Circle)
    (arcs : ι → Set Circle) (u v : ι → Circle)
    (hOpen : ∀ i, IsOpen (arcs i))
    (hConnected : ∀ i, IsConnected (arcs i))
    (_hProper : ∀ i, arcs i ≠ Set.univ)
    (hEndpoints : ∀ i, frontier (arcs i) = {u i, v i})
    (hDistinct : ∀ i, u i ≠ v i)
    (hArcsDisjoint : Pairwise fun i j ↦ Disjoint (arcs i) (arcs j))
    (_hAvoid : ∀ i, Disjoint (openSegment ℝ (σ (u i)) (σ (v i))) (Set.range σ))
    (_hChordsDisjoint : Pairwise fun i j ↦
      Disjoint (openSegment ℝ (σ (u i)) (σ (v i)))
        (openSegment ℝ (σ (u j)) (σ (v j))))
    (i : ℕ → ι) (x : ℕ → ℂ) (z : ℂ)
    (hi : Pairwise fun n m ↦ i n ≠ i m)
    (hx : ∀ n, x n ∈ segment ℝ (σ (u (i n))) (σ (v (i n))))
    (hz : Tendsto x atTop (𝓝 z)) :
    z ∈ Set.range σ := by
  have hend := accumulatingChord_endpoint_distance_tendsto_zero σ hσ.continuous
    arcs u v hOpen hConnected hEndpoints hDistinct hArcsDisjoint i hi
  have hclose : Tendsto (fun n ↦ dist (x n) (σ (u (i n)))) atTop (𝓝 0) := by
    refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_) hend
    exact Metric.mem_closedBall.mp (segment_subset_closedBall_left _ _ (hx n))
  exact (isCompact_range hσ.continuous).isClosed.mem_of_tendsto (hz.congr_dist hclose)
    (Eventually.of_forall (fun n ↦ ⟨u (i n), rfl⟩))


end HolomorphicAnosov
