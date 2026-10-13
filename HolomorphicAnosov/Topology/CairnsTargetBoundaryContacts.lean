import HolomorphicAnosov.Topology.CairnsStageGeometry
import HolomorphicAnosov.Topology.CairnsLiteralCarrierProperties
import HolomorphicAnosov.Topology.ConvexCapComponent

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- The prescribed target boundary parametrization is an embedding onto the
unit circle, whose bounded complementary component is the open unit disk.
These are the original-domain hypotheses for selecting target residual sectors.
Source: Cairns §4(C), target construction on the round disk. -/
theorem cairns_target_boundary_geometry
    {σ : Circle → ℂ} (hσ : Topology.IsEmbedding σ) (h : range σ ≃ₜ Circle) :
    let τ := fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)
    Topology.IsEmbedding τ ∧ range τ = range (fun z : Circle ↦ (z : ℂ)) ∧
      (∃ x ∈ Metric.ball (0 : ℂ) 1,
        connectedComponentIn (range τ)ᶜ x = Metric.ball (0 : ℂ) 1) := by
  intro τ
  let e : Circle ≃ₜ Circle := hσ.toHomeomorph.trans h
  have hemb : Topology.IsEmbedding τ := Topology.IsEmbedding.subtypeVal.comp e.isEmbedding
  have hrange : range τ = Metric.sphere (0 : ℂ) 1 := by
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      exact (e t).property
    · intro hz
      let zc : Circle := ⟨z,hz⟩
      exact ⟨e.symm zc,congrArg Subtype.val (e.apply_symm_apply zc)⟩
  have hk : range (fun z : Circle ↦ (z : ℂ)) = Metric.sphere (0 : ℂ) 1 := Subtype.range_coe
  refine ⟨hemb,hrange.trans hk.symm,0,by simp,?_⟩
  rw [hrange]
  have hh := convex_cap_component (univ : Set ℂ) convex_univ 0 1 0 ⟨mem_univ _,by simp⟩
  simpa only [compl_eq_univ_sdiff, univ_inter] using hh

/-- A stage's target boundary contacts are exactly its original retained
parameters. The carrier homeomorphism maps its source region onto its literal
image and therefore transports closures; on the original curve it is the
prescribed boundary map. Source: Cairns §4(C), matching source and target gaps. -/
theorem cairns_target_stage_contacts
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (h : range σ ≃ₜ Circle) (hs : StageGeometry σ a h s) :
    let τ := fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)
    τ ⁻¹' closure s.target = s.contacts σ := by
  intro τ
  obtain ⟨H,hH⟩ := hs.carrier
  have hi := (literal_carrier_homeomorph_properties _ _ s.map H hH).2.2 s.region
    (subset_closure.trans subset_union_left)
  have hcl := homeomorph_carriers_closure_iff _ _ s.region s.target
    (subset_closure.trans subset_union_left) (subset_closure.trans subset_union_left) H hi
  ext t
  have hh := hcl ⟨σ t,Or.inr (mem_range_self t)⟩
  rw [hH,hs.curve _ (mem_range_self t)] at hh
  exact hh.symm

end HolomorphicAnosov.Topology.Plane

