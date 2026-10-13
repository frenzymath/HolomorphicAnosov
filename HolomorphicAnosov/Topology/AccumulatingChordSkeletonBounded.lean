import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Convex.Segment

namespace HolomorphicAnosov
open Set

/-- The attached chord skeleton lies in the closed unit disk, hence is bounded. -/
theorem accumulatingChordSkeleton_bounded
    {ι : Type*} [Countable ι]
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (_h : (Set.range σ) ≃ₜ Circle)
    (arcs : ι → Set Circle) (u v : ι → Circle)
    (_hOpen : ∀ i, IsOpen (arcs i))
    (_hConnected : ∀ i, IsConnected (arcs i))
    (_hProper : ∀ i, arcs i ≠ Set.univ)
    (_hEndpoints : ∀ i, frontier (arcs i) = {u i, v i})
    (_hDistinct : ∀ i, u i ≠ v i)
    (_hArcsDisjoint : Pairwise fun i j ↦ Disjoint (arcs i) (arcs j))
    (_hAvoid : ∀ i, Disjoint (openSegment ℝ (σ (u i)) (σ (v i))) (Set.range σ))
    (_hChordsDisjoint : Pairwise fun i j ↦
      Disjoint (openSegment ℝ (σ (u i)) (σ (v i)))
        (openSegment ℝ (σ (u j)) (σ (v j)))) :
    Bornology.IsBounded (Set.range σ ∪ ⋃ i, segment ℝ (σ (u i)) (σ (v i))) := by
  obtain ⟨r, hr⟩ := (isCompact_range hσ.continuous).isBounded.subset_closedBall (0 : ℂ)
  apply (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).2
  refine ⟨r, ?_⟩
  intro z hz
  rcases hz with hz | hz
  · obtain ⟨p, rfl⟩ := hz
    exact hr ⟨p, rfl⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact (convex_closedBall (0 : ℂ) r).segment_subset
      (hr ⟨u i, rfl⟩) (hr ⟨v i, rfl⟩) hi


end HolomorphicAnosov
