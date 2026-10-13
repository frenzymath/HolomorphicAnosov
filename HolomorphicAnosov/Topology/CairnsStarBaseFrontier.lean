import HolomorphicAnosov.Topology.CairnsGeometricStarChoice
import HolomorphicAnosov.Topology.CairnsFrontBaseEndpoints
import HolomorphicAnosov.Topology.CairnsResidualStageContacts

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- The geometric star's outer front meets its base only at the base endpoints.
Its normalized direction map excludes the center and is injective. The
existing radial-front endpoint theorem then excludes every other base point. -/
theorem cairns_geometric_star_front_base_intersection
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (hσ : Topology.IsEmbedding σ) (b : StarChoice σ a g)
    (h : range σ ≃ₜ Circle) (hb : StarGeometry b h) :
    b.front ∩ segment ℝ (σ g.first) (σ g.last) = {σ g.first,σ g.last} := by
  rcases hb with ⟨hBne,hBopen,hBsub,hBfront,hLc,hBsweep,hBstar,hBunique,
    hCclosed,hCsub,hD₁,hD₂,hPC,hCurveCl,qs,hqs0,hqs1,horder,hpairs,hchords,
    hcompμ,hcompL,hcount,ds,hds,hrest⟩
  have hne : σ g.first ≠ σ g.last := by
    intro he
    have hh := (CairnsCircleGap.parameter_embedding_range g).1.injective
      (show g.parameter 0 = g.parameter 1 from
        (CairnsCircleGap.parameter_embedding_range g).2.2.1.trans
          ((hσ.injective he).trans (CairnsCircleGap.parameter_embedding_range g).2.2.2.symm))
    exact zero_ne_one hh
  have hcenter : (σ g.first + σ g.last) / 2 ∉ b.front := by
    intro hm
    have hh := hds ⟨(σ g.first + σ g.last) / 2,hm⟩
    have hn := Circle.norm_coe (ds ⟨(σ g.first + σ g.last) / 2,hm⟩)
    simp only [StarChoice.center,sub_self,norm_zero,Complex.ofReal_zero,div_zero] at hh
    rw [hh,norm_zero] at hn
    exact zero_ne_one hn
  apply Subset.antisymm
  · intro z hz
    apply cairns_front_base_endpoints _ _ b.contact b.front hne hD₁.1 hD₂.1 hcenter ds hds hz.1
    rw [segment_eq_image] at hz
    obtain ⟨t,ht,rfl⟩ := hz.2
    simp only [Complex.star_def,Complex.mul_im,Complex.conj_re,Complex.conj_im,
      Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
      Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]
    ring
  · intro z hz
    rcases hz with rfl | rfl
    · exact ⟨hD₁.1,left_mem_segment ℝ _ _⟩
    · exact ⟨hD₂.1,right_mem_segment ℝ _ _⟩

/-- The first contact is not on the old base chord. Interior base points lie
in the original complementary component; the contact lies on the curve and
has a strictly interior angular parameter, so it is neither base endpoint. -/
theorem cairns_star_contact_notMem_base
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (hσ : Topology.IsEmbedding σ) (b : StarChoice σ a g)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (hchord : openSegment ℝ (σ g.first) (σ g.last) ⊆ a) :
    b.contact ∉ segment ℝ (σ g.first) (σ g.last) := by
  intro hc
  have hne := cairns_star_contact_parameter_ne_endpoints b
  have hfirst : σ g.first ≠ b.contact := fun he ↦ hne.1 (hσ.injective he.symm)
  have hlast : σ g.last ≠ b.contact := fun he ↦ hne.2 (hσ.injective he.symm)
  have hmem := hchord (mem_openSegment_of_ne_left_right hfirst hlast hc)
  obtain ⟨x,hx,heq⟩ := ha
  have hmem' : b.contact ∈ connectedComponentIn (range σ)ᶜ x := heq.symm ▸ hmem
  exact connectedComponentIn_subset _ _ hmem' ⟨g.parameter b.contactParameter,rfl⟩

end HolomorphicAnosov.Topology.Plane
