import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Convex.Segment
import HolomorphicAnosov.Topology.AccumulatingChordSkeletonBounded
import HolomorphicAnosov.Topology.AccumulatingChordSkeletonClosed

namespace HolomorphicAnosov
open Set

/-- Compactness of the attached chord skeleton in Cairns' countable-chord
construction. Source: Cairns (1951), §3(E)--§4(A), pp.863--864, with the
countable accumulating-family compactness argument expanded using the null
closed-chord family described by de Carvalho, Definition 4.3 and Lemma 4.4,
pp.29--30. The proof is intentionally a named obligation: finite subfamilies
are compact by closed interval images, while an arbitrary convergent sequence
on distinct chords has endpoints converging to the base circle. -/
theorem accumulatingChordSkeleton_compact
    {ι : Type*} [Countable ι]
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (h : (Set.range σ) ≃ₜ Circle)
    (arcs : ι → Set Circle) (u v : ι → Circle)
    (hOpen : ∀ i, IsOpen (arcs i))
    (hConnected : ∀ i, IsConnected (arcs i))
    (hProper : ∀ i, arcs i ≠ Set.univ)
    (hEndpoints : ∀ i, frontier (arcs i) = {u i, v i})
    (hDistinct : ∀ i, u i ≠ v i)
    (hArcsDisjoint : Pairwise fun i j ↦ Disjoint (arcs i) (arcs j))
    (hAvoid : ∀ i, Disjoint (openSegment ℝ (σ (u i)) (σ (v i))) (Set.range σ))
    (hChordsDisjoint : Pairwise fun i j ↦
      Disjoint (openSegment ℝ (σ (u i)) (σ (v i)))
        (openSegment ℝ (σ (u j)) (σ (v j)))) :
    IsCompact (Set.range σ ∪ ⋃ i, segment ℝ (σ (u i)) (σ (v i))) := by
  have hb := accumulatingChordSkeleton_bounded σ hσ h arcs u v hOpen hConnected hProper
    hEndpoints hDistinct hArcsDisjoint hAvoid hChordsDisjoint
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨
    accumulatingChordSkeleton_closed σ hσ h arcs u v hOpen hConnected hProper
      hEndpoints hDistinct hArcsDisjoint hAvoid hChordsDisjoint, hb⟩


end HolomorphicAnosov
