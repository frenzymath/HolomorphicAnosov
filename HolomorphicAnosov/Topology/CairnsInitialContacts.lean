import HolomorphicAnosov.Topology.CairnsGeometricStarChoice

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- With the initial closure union, its contacts are exactly the union of the
two star-front contacts. On each original closed parameter arc only that
star's contacts occur: the opposite arc meets it only at the endpoints, which
are contacts of both stars. This is the local/global contact compatibility
needed to interpret both fronts' gap chords as actual stage gaps. -/
theorem cairns_initial_contacts_on_arcs
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle}
    (hσ : Topology.IsEmbedding σ) (h : range σ ≃ₜ Circle) (d : InitialData σ a p q)
    (h₁ : StarGeometry d.firstStar h) (h₂ : StarGeometry d.secondStar h)
    (hcl : closure (d.stage h).region =
      closure d.firstStar.sourceStar ∪ closure d.secondStar.sourceStar) :
    (d.stage h).contacts σ = σ ⁻¹' (d.firstStar.front ∩ range σ) ∪
      σ ⁻¹' (d.secondStar.front ∩ range σ) ∧
    (∀ t ∈ d.firstGap.closedArc, t ∈ (d.stage h).contacts σ ↔
      σ t ∈ d.firstStar.front ∩ range σ) ∧
    (∀ t ∈ d.secondGap.closedArc, t ∈ (d.stage h).contacts σ ↔
      σ t ∈ d.secondStar.front ∩ range σ) := by
  have hdata {g : CairnsCircleGap} (b : StarChoice σ a g) (hb : StarGeometry b h) :
      (range σ ∩ closure b.sourceStar = b.front ∩ range σ) ∧
      σ ⁻¹' (b.front ∩ range σ) ⊆ g.closedArc ∧
      σ g.first ∈ b.front ∩ range σ ∧ σ g.last ∈ b.front ∩ range σ := by
    have hsub : b.front ∩ range σ ⊆ σ '' range g.parameter := hb.2.2.2.2.2.2.2.2.2.1
    refine ⟨hb.2.2.2.2.2.2.2.2.2.2.2.2.2.1,?_,
      hb.2.2.2.2.2.2.2.2.2.2.1,hb.2.2.2.2.2.2.2.2.2.2.2.1⟩
    intro t ht
    obtain ⟨u,hu,he⟩ := hsub ht
    have hut : u = t := hσ.injective he
    rw [← hut,← (CairnsCircleGap.parameter_embedding_range g).2.1]
    exact hu
  obtain ⟨hcurve₁,hsub₁,hp₁,hq₁⟩ := hdata d.firstStar h₁
  obtain ⟨hcurve₂,hsub₂,hp₂,hq₂⟩ := hdata d.secondStar h₂
  have hT : (d.stage h).contacts σ = σ ⁻¹' (d.firstStar.front ∩ range σ) ∪
      σ ⁻¹' (d.secondStar.front ∩ range σ) := by
    ext t
    change σ t ∈ closure (d.stage h).region ↔ _
    rw [hcl]
    have htc : σ t ∈ range σ := mem_range_self t
    have hmem₁ : σ t ∈ closure d.firstStar.sourceStar ↔ σ t ∈ d.firstStar.front ∩ range σ := by
      rw [← hcurve₁]
      exact (and_iff_right htc).symm
    have hmem₂ : σ t ∈ closure d.secondStar.sourceStar ↔ σ t ∈ d.secondStar.front ∩ range σ := by
      rw [← hcurve₂]
      exact (and_iff_right htc).symm
    exact or_congr hmem₁ hmem₂
  have hf₂ : d.secondGap.first = d.firstGap.last := by
    change Circle.exp d.secondGap.start = Circle.exp d.firstGap.stop
    rw [d.second_start]
  have hl₂ : d.secondGap.last = d.firstGap.first := by
    change Circle.exp d.secondGap.stop = Circle.exp d.firstGap.start
    rw [d.second_stop,Circle.periodic_exp]
  have hmeet := (CairnsCircleGap.opposite_parameter_cover_inter d.firstGap d.secondGap
    d.second_start d.second_stop hf₂ hl₂).2
  rw [(CairnsCircleGap.parameter_embedding_range d.firstGap).2.1,
    (CairnsCircleGap.parameter_embedding_range d.secondGap).2.1] at hmeet
  refine ⟨hT,?_,?_⟩
  · intro t ht
    rw [hT]
    constructor
    · rintro (hc | hc)
      · exact hc
      · have he : t ∈ ({d.firstGap.first,d.firstGap.last} : Set Circle) :=
          hmeet ▸ (show t ∈ d.firstGap.closedArc ∩ d.secondGap.closedArc from ⟨ht,hsub₂ hc⟩)
        rcases he with rfl | rfl
        · exact hp₁
        · exact hq₁
    · exact Or.inl
  · intro t ht
    rw [hT]
    constructor
    · rintro (hc | hc)
      · have he : t ∈ ({d.firstGap.first,d.firstGap.last} : Set Circle) :=
          hmeet ▸ (show t ∈ d.firstGap.closedArc ∩ d.secondGap.closedArc from ⟨hsub₁ hc,ht⟩)
        rcases he with rfl | rfl
        · simpa only [hl₂] using hq₂
        · simpa only [hf₂] using hp₂
      · exact hc
    · exact Or.inr

end HolomorphicAnosov.Topology.Plane
