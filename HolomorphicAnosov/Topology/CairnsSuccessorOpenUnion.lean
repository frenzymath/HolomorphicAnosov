import HolomorphicAnosov.Topology.CairnsResidualStarRefinement

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- If each old-region/star/seam union is open, their union is the literal
successor region. The old region is included separately so this argument also
covers a stage with no residual gaps. Source: Cairns §4(C), equation (4.3). -/
theorem cairns_successor_open_of_local_gluing
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (d : StepData σ a s) (h : range σ ≃ₜ Circle) (hs : IsOpen s.region)
    (hlocal : ∀ i, IsOpen (s.region ∪ (d.star i).sourceStar ∪
      openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last))) :
    IsOpen (d.next h).region := by
  have heq : (d.next h).region = s.region ∪ ⋃ i,
      (s.region ∪ (d.star i).sourceStar ∪
        openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last)) := by
    ext z
    simp only [StepData.next,mem_union,mem_iUnion]
    constructor
    · rintro (hz | ⟨i,hi | hi⟩)
      · exact Or.inl hz
      · exact Or.inr ⟨i,Or.inl (Or.inr hi)⟩
      · exact Or.inr ⟨i,Or.inr hi⟩
    · rintro (hz | ⟨i,(hi | hi) | hi⟩)
      · exact Or.inl hz
      · exact Or.inl hi
      · exact Or.inr ⟨i,Or.inl hi⟩
      · exact Or.inr ⟨i,Or.inr hi⟩
  rw [heq]
  exact hs.union (isOpen_iUnion hlocal)

end HolomorphicAnosov.Topology.Plane

