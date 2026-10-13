import HolomorphicAnosov.Topology.CairnsResidualStarRefinement

/-!
# The first perpendicular contact belongs to the sector closure

Source: Cairns (1951), §3(D), printed pp.862–863, the first contact along the
perpendicular ray; used in the corollary to Lemma 4.1, printed p.865.
-/

namespace HolomorphicAnosov.Topology.Plane

open Set CairnsRefinement

/-- Every chosen residual sector has a closure point on the original embedded curve.

Source: Cairns (1951), §3(D), pp.862–863. The open perpendicular ray from the
chord midpoint stays inside the sector until its positive first-contact radius.
Continuity of this affine ray puts its endpoint in the sector closure, and the
first-contact equation identifies that endpoint with the specified original curve point.
This uses only the first-contact data and does not assume the star-extension theorem. -/
theorem cairns_star_sector_boundary_contact
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (b : StarChoice σ a g) : (closure b.sector ∩ range σ).Nonempty := by
  let f : ℝ → ℂ := fun t ↦ (σ g.first + σ g.last) / 2 +
    t • (b.sign • (Complex.I * (σ g.last - σ g.first)))
  have hf : Continuous f := by fun_prop
  have hr : b.radius ∈ closure (Ioo (0 : ℝ) b.radius) := by
    rw [closure_Ioo b.radius_pos.ne]
    exact ⟨b.radius_pos.le, le_rfl⟩
  have hmem : f b.radius ∈ closure b.sector :=
    hf.continuousWithinAt.mem_closure hr (fun t ht ↦ b.ray_inside t ht)
  refine ⟨σ (g.parameter b.contactParameter), ?_, ⟨g.parameter b.contactParameter, rfl⟩⟩
  simpa only [f, b.first_contact] using hmem

end HolomorphicAnosov.Topology.Plane

