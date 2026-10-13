import HolomorphicAnosov.Topology.CairnsRadialPatchConvexControl
import HolomorphicAnosov.Topology.CairnsResidualStarRecurrenceProperties
import HolomorphicAnosov.Topology.CairnsStarSectorBoundaryContact
import HolomorphicAnosov.Topology.CairnsShrinkingResidualExhaustion
import HolomorphicAnosov.Topology.AccumulatingChordContinuity
import HolomorphicAnosov.Topology.CairnsNormalizedCircleGap
import HolomorphicAnosov.Topology.Plane.CairnsChordSectorSeparation
import HolomorphicAnosov.Topology.Plane.CairnsConvexStarSectorExtension
import HolomorphicAnosov.Topology.CairnsResidualStarRefinement
import HolomorphicAnosov.Topology.CairnsGapMeshEmpty
import HolomorphicAnosov.Topology.CairnsResidualSectorInvariantG20
import HolomorphicAnosov.Topology.CairnsResidualChordRefinementSchedule

namespace HolomorphicAnosov.Topology.Plane

open Set CairnsStar CairnsRefinement

/-!
Named source-backed construction obligation used by the public provider.

Source: Cairns (1951), §4(B),(C), pp.864–865, recurrent Hypothesis (1)–(5),
equations (4.3),(4.4), Lemma 4.1 and corollary.  The simultaneous recurrence
construction is deferred here as an explicit theorem so its source obligation
can be completed independently of the consumer-facing wrapper.
DAG node: topo.cairns_residual_chord_refinement_construction_core_g20.
-/
theorem cairns_residual_chord_refinement_construction_source_obligation
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (a : Set ℂ) (ha : a.Nonempty) (haBounded : Bornology.IsBounded a)
    (haComponent : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (h : (range σ) ≃ₜ Circle) (p q : Circle) (hpq : p ≠ q)
    (hChord : openSegment ℝ (σ p) (σ q) ⊆ a)
    (hCore : p = p) :
    let k := range (fun z : Circle ↦ (z : ℂ))
    let targetBoundary := fun t : Circle ↦ (h ⟨σ t, ⟨t, rfl⟩⟩ : ℂ)
    ∃ d : Data σ a p q h,
      let A := fun j ↦ (d.stages j).region
      let K := fun j ↦ (d.stages j).target
      let T := fun j ↦ (d.stages j).contacts σ
      let I := fun j ↦ ResidualComponent (T j)
      let gap := fun j (i : I j) ↦ (d.steps j).gap i
      let β := fun j (i : I j) ↦ ((d.steps j).star i).sector
      ∃ βt : ∀ j, I j → Set ℂ,
        (∀ j, (A j).Nonempty ∧ IsOpen (A j) ∧ A j ⊆ a ∧
          Nonempty ((A j) ≃ₜ Metric.ball (0 : ℂ) 1) ∧
          (K j).Nonempty ∧ IsOpen (K j) ∧ K j ⊆ Metric.ball (0 : ℂ) 1) ∧
        Monotone A ∧ Monotone K ∧ Monotone T ∧
        (∀ j, IsClosed (T j) ∧
          ∃ t₁ t₂ t₃ t₄ : Circle, t₁ ∈ T j ∧ t₂ ∈ T j ∧ t₃ ∈ T j ∧ t₄ ∈ T j ∧
            t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₁ ≠ t₄ ∧ t₂ ≠ t₃ ∧ t₂ ≠ t₄ ∧ t₃ ≠ t₄) ∧
        Dense (⋃ j, T j) ∧ closure (⋃ j, σ '' T j) = range σ ∧
        (∀ j, Set.Countable {U : Set Circle |
          ∃ x ∈ (T j)ᶜ, connectedComponentIn (T j)ᶜ x = U}) ∧
        (∀ j, Nonempty (Circle ≃ₜ frontier (A j)) ∧
          frontier (A j) = σ '' T j ∪
            ⋃ i : I j, openSegment ℝ (σ (gap j i).first) (σ (gap j i).last) ∧
          frontier (K j) = targetBoundary '' T j ∪
            ⋃ i : I j, openSegment ℝ (targetBoundary (gap j i).first)
              (targetBoundary (gap j i).last)) ∧
        (∀ j, ∃ H : ↥(closure (A j) ∪ range σ) ≃ₜ ↥(closure (K j) ∪ k),
          (∀ x, (H x : ℂ) = (d.stages j).map x) ∧
          (∀ (x : ↥(closure (A j) ∪ range σ)) (hx : (x : ℂ) ∈ range σ),
            (H x : ℂ) = (h ⟨x, hx⟩ : ℂ))) ∧
        (∀ j z, z ∈ closure (A j) ∪ range σ →
          (d.stages (j + 1)).map z = (d.stages j).map z) ∧
        (∀ j (i : I j) (t : CairnsStar.I),
          (d.stages j).map ((1 - (t : ℝ)) • σ (gap j i).first +
            (t : ℝ) • σ (gap j i).last) =
          (1 - (t : ℝ)) • targetBoundary (gap j i).first +
            (t : ℝ) • targetBoundary (gap j i).last) ∧
        (∀ j, T (j + 1) = T j ∪
          ⋃ i : I j, σ ⁻¹' (((d.steps j).star i).front ∩ range σ)) ∧
        (∀ j, K (j + 1) = K j ∪
          ⋃ i : I j, (((d.steps j).star i).targetStar h ∪
            openSegment ℝ (targetBoundary (gap j i).first)
              (targetBoundary (gap j i).last))) ∧
        (∀ j, a \ closure (A j) = ⋃ i : I j, β j i) ∧
        (∀ j, Metric.ball (0 : ℂ) 1 \ closure (K j) = ⋃ i : I j, βt j i) ∧
        (∀ j, Pairwise (fun i i' : I j ↦ Disjoint (β j i) (β j i')) ∧
          Pairwise (fun i i' : I j ↦ Disjoint (βt j i) (βt j i'))) ∧
        (∀ j (i : I j),
          (β j i).Nonempty ∧ IsOpen (β j i) ∧ IsConnected (β j i) ∧
          (∃ x ∈ a \ closure (A j),
            connectedComponentIn (a \ closure (A j)) x = β j i) ∧
          frontier (β j i) ⊆ segment ℝ (σ (gap j i).first) (σ (gap j i).last) ∪
            σ '' (gap j i).closedArc ∧
          (∀ z r, σ '' (gap j i).closedArc ⊆ Metric.closedBall z r →
            closure (β j i) ⊆ Metric.closedBall z r) ∧
          (βt j i).Nonempty ∧ IsOpen (βt j i) ∧ IsConnected (βt j i) ∧
          (∃ x ∈ Metric.ball (0 : ℂ) 1 \ closure (K j),
            connectedComponentIn (Metric.ball (0 : ℂ) 1 \ closure (K j)) x = βt j i) ∧
          frontier (βt j i) ⊆
            segment ℝ (targetBoundary (gap j i).first) (targetBoundary (gap j i).last) ∪
              targetBoundary '' (gap j i).closedArc ∧
          (∀ z r, targetBoundary '' (gap j i).closedArc ⊆ Metric.closedBall z r →
            closure (βt j i) ⊆ Metric.closedBall z r) ∧
          targetBoundary '' (gap j i).closedArc ⊆ closure (βt j i) ∧
          (∀ n : ℕ, j ≤ n →
            MapsTo (d.stages n).map (A n ∩ β j i) (closure (βt j i)))) ∧
        (∀ j, (¬ ∃ g : CairnsCircleGap, g.IsGapOf (T j)) →
          CairnsCircleGap.mesh (T j) = 0) ∧
        (∀ j, (∃ g : CairnsCircleGap, g.IsGapOf (T j)) →
          ∃ g : CairnsCircleGap, g.IsGapOf (T j) ∧
            g.normalizedLength = CairnsCircleGap.mesh (T j)) ∧
        Filter.Tendsto (fun j ↦ CairnsCircleGap.mesh (T j)) Filter.atTop (nhds 0) ∧
        (∀ ε > 0, ∃ J : ℕ, ∀ j ≥ J, ∀ i : I j,
          Metric.diam (closure (β j i)) < ε ∧ Metric.diam (closure (βt j i)) < ε) ∧
        (∀ j (i : I j), (closure (β j i) ∩ range σ).Nonempty ∧
          (closure (βt j i) ∩ k).Nonempty)
        ∧ (∀ _j : ℕ, True) := by
  exact cairns_residual_chord_refinement_schedule_source_obligation
    σ hσ a ha haBounded haComponent h p q hpq hChord hCore trivial

end HolomorphicAnosov.Topology.Plane
