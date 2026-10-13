import HolomorphicAnosov.Topology.CairnsStarPatchHomeomorph
import HolomorphicAnosov.Topology.CairnsLiteralCarrierProperties

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- The target successor closure is the old target closure plus all new
closed target stars. The source closure is already the compact union of old
closure and closed stars, and continuity identifies its image with the image
region's closure. Literal old-map agreement and patch bijectivity then identify
every image piece. Source: Cairns §4(C), closed carrier recurrence. -/
theorem cairns_successor_target_closure
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (d : StepData σ a s) (h : range σ ≃ₜ Circle)
    (hgeo : ∀ i, StarGeometry (d.star i) h)
    (hpatch : ∀ i z, z ∈ closure (d.star i).sourceStar →
      (d.next h).map z = (d.star i).patchMap h z)
    (hcl : closure (d.next h).region = closure s.region ∪ ⋃ i, closure (d.star i).sourceStar)
    (hc : IsCompact (closure (d.next h).region))
    (hcont : ContinuousOn (d.next h).map (closure (d.next h).region))
    (holdimage : s.map '' closure s.region = closure s.target) :
    closure (d.next h).target = closure s.target ∪ ⋃ i, closure ((d.star i).targetStar h) := by
  classical
  have hold : ∀ z ∈ closure s.region, (d.next h).map z = s.map z := by
    intro z hz
    change (if z ∈ closure s.region ∪ range σ then s.map z else _) = _
    exact ite_eq_left (Or.inl hz)
  unfold Stage.target
  rw [← image_closure_eq_of_compact_closure (d.next h).region (d.next h).map hc hcont,
    hcl,image_union,image_iUnion]
  congr 1
  · exact (image_congr hold).trans holdimage
  · apply iUnion_congr
    intro i
    exact (image_congr (hpatch i)).trans (cairns_star_patch_bijOn (d.star i) h (hgeo i)).2.1.image_eq

end HolomorphicAnosov.Topology.Plane

