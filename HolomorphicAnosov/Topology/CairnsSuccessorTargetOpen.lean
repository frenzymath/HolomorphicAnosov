import HolomorphicAnosov.Topology.CairnsResidualStarRefinement
import HolomorphicAnosov.Topology.CairnsClosedCellRestriction

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- A carrier homeomorphism transports an open source region to an open target
region. The equality of literal values identifies that image with the stage
image definition, so no separate openness argument is needed for the target.
Source: Cairns §4(C), target recurrence. -/
theorem cairns_target_open_of_carrier_homeomorph
    {s t : Stage} {σ : Circle → ℂ}
    (H : ↥(closure s.region ∪ Set.range σ) ≃ₜ
      ↥(closure t.region ∪ Set.range (fun z : Circle ↦ (z : ℂ))))
    (hH : ∀ x, (H x : ℂ) = s.map x)
    (hsource : IsOpen s.region)
    (hregion : t.region = s.map '' s.region) :
    IsOpen t.region := by
  let A := closure s.region ∪ Set.range σ
  let B := closure t.region ∪ Set.range (fun z : Circle ↦ (z : ℂ))
  have hUA : s.region ⊆ A := subset_closure.trans subset_union_left
  have himage :
      (fun x : A ↦ (H x : ℂ)) '' (Subtype.val ⁻¹' s.region) = t.region := by
    apply Eq.trans _ hregion.symm
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x.val,hx,(hH x).symm⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hUA hx⟩,hx,hH ⟨x,hUA hx⟩⟩
  rw [← himage]
  exact carrier_homeomorph_open_image A B s.region H hsource hUA

end HolomorphicAnosov.Topology.Plane

