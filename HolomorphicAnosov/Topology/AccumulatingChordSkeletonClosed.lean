import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Convex.Segment
import HolomorphicAnosov.Topology.AccumulatingChordSkeletonClosedFinite
import HolomorphicAnosov.Topology.AccumulatingChordSkeletonClosedInfinite

namespace HolomorphicAnosov
open Set

/-- The attached chord skeleton is closed. The source proof is the null-family
argument: a limit on distinct chord pieces has endpoints converging to the
base embedded circle, while a recurring chord reduces to its closed segment. -/
theorem accumulatingChordSkeleton_closed
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
    IsClosed (Set.range σ ∪ ⋃ i, segment ℝ (σ (u i)) (σ (v i))) := by
  classical
  by_cases hfin : Finite ι
  · let := hfin
    exact accumulatingChordSkeleton_closed_of_finite σ hσ arcs u v
  · let := not_finite_iff_infinite.mp hfin
    exact accumulatingChordSkeleton_closed_of_infinite σ hσ h arcs u v hOpen hConnected hProper
      hEndpoints hDistinct hArcsDisjoint hAvoid hChordsDisjoint


end HolomorphicAnosov
