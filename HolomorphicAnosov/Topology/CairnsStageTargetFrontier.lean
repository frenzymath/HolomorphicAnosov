import HolomorphicAnosov.Topology.CairnsFrontierImage
import HolomorphicAnosov.Topology.CairnsSuccessorTargetImage
import HolomorphicAnosov.Topology.CairnsGapSupportingChord

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- The stage's literal map transports its source contact-and-chord frontier
to the corresponding target frontier. Compact closure continuity identifies
frontier images; the prescribed curve map and affine chord formulas identify
each piece. Source: Cairns §4(C), equations (4.3)–(4.4). -/
theorem cairns_stage_target_frontier
    {σ : Circle → ℂ} (s : Stage) (h : range σ ≃ₜ Circle)
    (hc : IsCompact (closure s.region)) (hcont : ContinuousOn s.map (closure s.region))
    (hinj : InjOn s.map (closure s.region)) (hsopen : IsOpen s.region) (htopen : IsOpen s.target)
    (hcurve : ∀ (z : ℂ) (hz : z ∈ range σ), s.map z = (h ⟨z,hz⟩ : ℂ))
    (gap : ResidualComponent (s.contacts σ) → CairnsCircleGap)
    (hfront : frontier s.region = σ '' s.contacts σ ∪
      ⋃ i, openSegment ℝ (σ (gap i).first) (σ (gap i).last))
    (haff : ∀ i (t : I),
      s.map ((1-(t : ℝ)) • σ (gap i).first + (t : ℝ) • σ (gap i).last) =
        (1-(t : ℝ)) • (h ⟨σ (gap i).first,⟨(gap i).first,rfl⟩⟩ : ℂ) +
          (t : ℝ) • (h ⟨σ (gap i).last,⟨(gap i).last,rfl⟩⟩ : ℂ)) :
    frontier s.target = (fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)) '' s.contacts σ ∪
      ⋃ i, openSegment ℝ (h ⟨σ (gap i).first,⟨(gap i).first,rfl⟩⟩ : ℂ)
        (h ⟨σ (gap i).last,⟨(gap i).last,rfl⟩⟩ : ℂ) := by
  unfold Stage.target
  rw [← compact_closure_frontier_image s.region s.map hc hcont hinj hsopen htopen,
    hfront,image_union,image_iUnion,image_image]
  congr 1
  · apply image_congr
    intro t ht
    exact hcurve (σ t) (mem_range_self t)
  · apply iUnion_congr
    intro i
    exact affine_chord_image_openSegment _ _ _ _ _ (haff i)

/-- A stage with the target contact-and-chord frontier fills the interior of
its compact contact hull. Its nonempty open target is bounded in the unit disk;
supporting gap chords place its entire frontier on the contact-hull frontier.
The closure is therefore the same hull. Source: Cairns §4(C), convex target
stage invariant. -/
theorem cairns_stage_target_contact_hull
    {σ : Circle → ℂ} (hσ : Topology.IsEmbedding σ) (s : Stage) (h : range σ ≃ₜ Circle)
    (hne : s.target.Nonempty) (hopen : IsOpen s.target)
    (hball : s.target ⊆ Metric.ball (0 : ℂ) 1)
    (hTclosed : IsClosed (s.contacts σ)) (hTne : (s.contacts σ).Nonempty)
    (gap : ResidualComponent (s.contacts σ) → CairnsCircleGap)
    (hgap : ∀ i, (gap i).IsGapOf (s.contacts σ))
    (hfront : frontier s.target = (fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)) '' s.contacts σ ∪
      ⋃ i, openSegment ℝ (h ⟨σ (gap i).first,⟨(gap i).first,rfl⟩⟩ : ℂ)
        (h ⟨σ (gap i).last,⟨(gap i).last,rfl⟩⟩ : ℂ)) :
    let τ := fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)
    s.target = interior (convexHull ℝ (τ '' s.contacts σ)) ∧
      closure s.target = convexHull ℝ (τ '' s.contacts σ) ∧ Convex ℝ s.target ∧
      Nonempty (s.target ≃ₜ Metric.ball (0 : ℂ) 1) ∧
      Nonempty (frontier s.target ≃ₜ Metric.sphere (0 : ℂ) 1) := by
  intro τ
  have hτ : Continuous τ := continuous_subtype_val.comp
    (h.continuous.comp (hσ.continuous.subtype_mk (fun t ↦ ⟨t,rfl⟩)))
  have hτinj : Function.Injective τ := by
    intro u v he
    exact hσ.injective (congrArg Subtype.val (h.injective (Subtype.ext he)))
  have hτnorm : ∀ t, ‖τ t‖ = 1 := fun t ↦ Circle.norm_coe _
  have hf : frontier s.target ⊆ τ '' s.contacts σ ∪
      ⋃ i, segment ℝ (τ (gap i).first) (τ (gap i).last) := by
    rw [hfront]
    apply union_subset subset_union_left
    apply iUnion_subset
    intro i z hz
    exact Or.inr (mem_iUnion.mpr ⟨i,openSegment_subset_segment ℝ _ _ hz⟩)
  obtain ⟨heq,hdisk,hcircle⟩ := cairns_contact_chord_region_eq_hull_interior τ hτ hτinj hτnorm
    (s.contacts σ) hTclosed hTne gap hgap s.target hopen hne
    ((Metric.isBounded_ball (x := (0 : ℂ)) (r := 1)).subset hball) hf
  have hcompact := isCompact_convexHull_finiteDimensional (hTclosed.isCompact.image hτ)
  have hclosure : closure s.target = convexHull ℝ (τ '' s.contacts σ) := by
    rw [heq,(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior (heq ▸ hne),
      hcompact.isClosed.closure_eq]
  exact ⟨heq,hclosure,heq.symm ▸ (convex_convexHull ℝ _).interior,hdisk,hcircle⟩

end HolomorphicAnosov.Topology.Plane

