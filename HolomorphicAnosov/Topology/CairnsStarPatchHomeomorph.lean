import HolomorphicAnosov.Topology.CairnsGeometricStarChoice
import HolomorphicAnosov.Topology.CairnsClosedCellRestriction

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- A geometric star extension restricts to a homeomorphism of the closed
source star onto the closed target star. The open-star correspondence from
the literal extension transports closures inside the carrier, and the
restricted map is exactly `patchMap`. -/
theorem cairns_star_patch_homeomorph
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (b : StarChoice σ a g) (h : range σ ≃ₜ Circle) (hb : StarGeometry b h) :
    ∃ H : closure b.sourceStar ≃ₜ closure (b.targetStar h),
      (∀ x, (H x : ℂ) = b.patchMap h x) := by
  obtain ⟨H,hmap,hopen⟩ := cairns_geometric_star_literal_extension b h hb
  have hcl : ∀ x : ↥(range σ ∪ closure b.sourceStar),
      (x : ℂ) ∈ closure b.sourceStar ↔
        (H x : ℂ) ∈ closure (b.targetStar h) := by
    intro x
    exact homeomorph_carriers_closure_iff _ _ b.sourceStar (b.targetStar h)
      (subset_closure.trans subset_union_right)
      (subset_closure.trans subset_union_right) H hopen.1 x
  let Hc := homeomorphRestrictSubsets
    (range σ ∪ closure b.sourceStar)
    (range (fun z : Circle ↦ (z : ℂ)) ∪ closure (b.targetStar h))
    (closure b.sourceStar) (closure (b.targetStar h))
    subset_union_right subset_union_right H hcl
  refine ⟨Hc,?_⟩
  intro x
  exact hmap ⟨x,Or.inr x.property⟩

/-- The literal patch is a continuous bijection on each closed star and maps
its open star onto the target star. These are the patchwise hypotheses for
the simultaneous compact gluing construction. -/
theorem cairns_star_patch_bijOn
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (b : StarChoice σ a g) (h : range σ ≃ₜ Circle) (hb : StarGeometry b h) :
    ContinuousOn (b.patchMap h) (closure b.sourceStar) ∧
      BijOn (b.patchMap h) (closure b.sourceStar) (closure (b.targetStar h)) ∧
      b.patchMap h '' b.sourceStar = b.targetStar h := by
  obtain ⟨G,hG⟩ := cairns_star_patch_homeomorph b h hb
  have hcont : ContinuousOn (b.patchMap h) (closure b.sourceStar) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hh := continuous_subtype_val.comp G.continuous
    convert hh using 1
    funext x
    exact (hG x).symm
  have hbij : BijOn (b.patchMap h) (closure b.sourceStar) (closure (b.targetStar h)) := by
    refine ⟨?_,?_,?_⟩
    · intro z hz
      rw [← hG ⟨z,hz⟩]
      exact (G ⟨z,hz⟩).property
    · intro x hx y hy he
      have hh : G ⟨x,hx⟩ = G ⟨y,hy⟩ := by
        apply Subtype.ext
        simpa only [hG] using he
      exact congrArg Subtype.val (G.injective hh)
    · intro y hy
      obtain ⟨x,hx⟩ := G.surjective ⟨y,hy⟩
      exact ⟨x,x.property,(hG x).symm.trans (congrArg Subtype.val hx)⟩
  refine ⟨hcont,hbij,?_⟩
  obtain ⟨H,hmap,hint,_⟩ := cairns_geometric_star_literal_extension b h hb
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [← hmap ⟨x,Or.inr (subset_closure hx)⟩]
    exact (hint _).mp hx
  · intro hy
    obtain ⟨x,hx⟩ := H.surjective ⟨y,Or.inr (subset_closure hy)⟩
    have hxy : (H x : ℂ) = y := congrArg Subtype.val hx
    exact ⟨x,(hint x).mpr (hxy.symm ▸ hy),(hmap x).symm.trans hxy⟩

end HolomorphicAnosov.Topology.Plane

