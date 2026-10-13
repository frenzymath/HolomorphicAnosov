import HolomorphicAnosov.Topology.CairnsGeometricStarChoice
import HolomorphicAnosov.Topology.CairnsSuccessorStarIntersection
import HolomorphicAnosov.Topology.CairnsSuccessorSectorDisjoint
import HolomorphicAnosov.Topology.CairnsSuccessorPatchAgreement

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- Each attached radial patch agrees with the old map on their common
carrier. On the original curve both take the prescribed boundary values.
The remaining overlap is the old base chord, where both maps are affine
with the same endpoint values. Source: Cairns §4(C), (4.2)–(4.3). -/
theorem cairns_successor_patch_agrees_old
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (d : StepData σ a s) (h : range σ ≃ₜ Circle)
    (hgeo : ∀ i, StarGeometry (d.star i) h)
    (hcurve : ∀ (z : ℂ) (hz : z ∈ range σ), s.map z = (h ⟨z,hz⟩ : ℂ))
    (hchord : ∀ i, openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆ closure s.region)
    (haff : ∀ i (t : I),
      s.map ((1-(t : ℝ)) • σ (d.gap i).first + (t : ℝ) • σ (d.gap i).last) =
        (1-(t : ℝ)) • (h ⟨σ (d.gap i).first,⟨(d.gap i).first,rfl⟩⟩ : ℂ) +
          (t : ℝ) • (h ⟨σ (d.gap i).last,⟨(d.gap i).last,rfl⟩⟩ : ℂ)) :
    ∀ i z, z ∈ closure (d.star i).sourceStar →
      z ∈ closure s.region ∪ range σ → s.map z = (d.star i).patchMap h z := by
  classical
  intro i z hz hold
  by_cases hc : z ∈ range σ
  · rw [hcurve z hc]
    simp only [StarChoice.patchMap, dite_eq_left hc]
  · have hzold : z ∈ closure s.region := hold.resolve_right hc
    have hbase : segment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆
        closure (d.star i).sourceStar := by
      intro w hw
      exact frontier_subset_closure ((hgeo i).2.2.2.1 ▸ Or.inl hw)
    have hzbase := cairns_successor_star_closure_intersection hσ ha d i
      (hgeo i).2.2.1 hbase (hchord i)
    have hzseg : z ∈ segment ℝ (σ (d.gap i).first) (σ (d.gap i).last) :=
      hzbase ▸ ⟨hzold,hz⟩
    rw [segment_eq_image] at hzseg
    obtain ⟨t,ht,rfl⟩ := hzseg
    obtain ⟨H,hH,hint,hbaseaff,hrest⟩ :=
      cairns_geometric_star_literal_extension (d.star i) h (hgeo i)
    exact (haff i ⟨t,ht⟩).trans (hbaseaff ⟨t,ht⟩).symm

/-- The literal successor map uses each attached star's radial extension
on its entire closed star, including shared seams and original contacts.
Disjoint outside sectors make different patches overlap only in the old
carrier, where the preceding compatibility theorem identifies their values.
Source: Cairns §4(C), well-defined extension in equation (4.3). -/
theorem cairns_successor_literal_patches
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (d : StepData σ a s) (h : range σ ≃ₜ Circle)
    (hgeo : ∀ i, StarGeometry (d.star i) h)
    (hcurve : ∀ (z : ℂ) (hz : z ∈ range σ), s.map z = (h ⟨z,hz⟩ : ℂ))
    (hchord : ∀ i, openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last) ⊆ closure s.region)
    (haff : ∀ i (t : I),
      s.map ((1-(t : ℝ)) • σ (d.gap i).first + (t : ℝ) • σ (d.gap i).last) =
        (1-(t : ℝ)) • (h ⟨σ (d.gap i).first,⟨(d.gap i).first,rfl⟩⟩ : ℂ) +
          (t : ℝ) • (h ⟨σ (d.gap i).last,⟨(d.gap i).last,rfl⟩⟩ : ℂ)) :
    ∀ i z, z ∈ closure (d.star i).sourceStar →
      (d.next h).map z = (d.star i).patchMap h z := by
  apply cairns_successor_map_eq_patch d h
  · exact cairns_successor_star_overlap_in_old_carrier hσ ha d
      (fun i ↦ (hgeo i).2.2.1) hchord
  · exact cairns_successor_patch_agrees_old hσ ha d h hgeo hcurve hchord haff

end HolomorphicAnosov.Topology.Plane

