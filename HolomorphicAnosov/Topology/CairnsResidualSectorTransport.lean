import HolomorphicAnosov.Topology.CairnsNestedSectorGaps
import HolomorphicAnosov.Topology.CairnsGeometricPatchConvexControl
import HolomorphicAnosov.Topology.CairnsSuccessorLiteralPatches
import HolomorphicAnosov.Topology.CairnsLiteralCarrierProperties
import HolomorphicAnosov.Topology.CairnsResidualStarRecurrenceProperties

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- Every later filled point in a fixed source residual sector is carried
into the convex hull of the corresponding original target arc. Induct over
later stages. Old closure points follow from the induction hypothesis by
continuity inside the open sector. New stars meeting that sector have nested
parameter arcs by component monotonicity and the first-contact label; convex
control of the radial patch puts their images in the same target hull. Old
seam points are already covered by the closure case. Source: Cairns §4(C),
transport of later patches in their original residual sectors. -/
theorem cairns_residual_sector_transport
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : range σ ≃ₜ Circle}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (d : Data σ a p q h)
    (hgeom : ∀ n, StageGeometry σ a h (d.stages n))
    (hstar : ∀ n i, StarGeometry ((d.steps n).star i) h)
    (j : ℕ) (i : ResidualComponent ((d.stages j).contacts σ)) (n : ℕ) (hjn : j ≤ n) :
    MapsTo (d.stages n).map ((d.stages n).region ∩ ((d.steps j).star i).sector)
      (convexHull ℝ ((fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)) ''
        ((d.steps j).gap i).closedArc)) := by
  classical
  let τ := fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)
  let β := ((d.steps j).star i).sector
  let C := convexHull ℝ (τ '' ((d.steps j).gap i).closedArc)
  have hτ : Continuous τ := continuous_subtype_val.comp
    (h.continuous.comp (hσ.continuous.subtype_mk (fun t ↦ ⟨t,rfl⟩)))
  have hCclosed : IsClosed C := (isCompact_convexHull_finiteDimensional
    ((isCompact_Icc.image Circle.exp.continuous).image hτ)).isClosed
  have hβopen : IsOpen β := (cairns_star_sector_geometry hσ ha ((d.steps j).star i)).2.1
  have hchord (m : ℕ) (k : ResidualComponent ((d.stages m).contacts σ)) :
      openSegment ℝ (σ ((d.steps m).gap k).first) (σ ((d.steps m).gap k).last) ⊆
        closure (d.stages m).region :=
    ((hgeom m).chord _ ((d.steps m).gap_isGap k)).trans
      (inter_subset_right.trans frontier_subset_closure)
  have hmono := (cairns_residual_star_recurrence_properties d).1
  change MapsTo (d.stages n).map ((d.stages n).region ∩ β) C
  induction n, hjn using Nat.le_induction with
  | base =>
      rintro z ⟨hz,hzβ⟩
      exact (disjoint_left.mp ((d.steps j).outside i) hzβ hz).elim
  | succ n hjn ih =>
      have hclosure : MapsTo (d.stages n).map (closure (d.stages n).region ∩ β) C := by
        rintro z ⟨hz,hzβ⟩
        obtain ⟨H,hH⟩ := (hgeom n).carrier
        have hc := (literal_carrier_homeomorph_properties _ _ (d.stages n).map H hH).1
        have hcz : ContinuousWithinAt (d.stages n).map ((d.stages n).region ∩ β) z :=
          (hc z (Or.inl hz)).mono (inter_subset_left.trans (subset_closure.trans subset_union_left))
        have hh : (d.stages n).map z ∈ closure C :=
          hcz.mem_closure (hβopen.closure_inter ⟨hz,hzβ⟩) ih
        exact hCclosed.closure_eq ▸ hh
      have hpatch := cairns_successor_literal_patches hσ ha (d.steps n) h (hstar n)
        (hgeom n).curve (hchord n) (fun k ↦ (hgeom n).affine _ ((d.steps n).gap_isGap k))
      rintro z ⟨hz,hzβ⟩
      rw [d.next_eq n] at hz ⊢
      by_cases hzold : z ∈ closure (d.stages n).region
      · have hold : ((d.steps n).next h).map z = (d.stages n).map z := by
          change (if z ∈ closure (d.stages n).region ∪ range σ then _ else _) = _
          rw [ite_eq_left (show z ∈ closure (d.stages n).region ∪ range σ from Or.inl hzold)]
        rw [hold]
        exact hclosure ⟨hzold,hzβ⟩
      · change z ∈ (d.stages n).region ∪ ⋃ k,
          (((d.steps n).star k).sourceStar ∪ openSegment ℝ
            (σ ((d.steps n).gap k).first) (σ ((d.steps n).gap k).last)) at hz
        rcases hz with hz | hz
        · exact (hzold (subset_closure hz)).elim
        · obtain ⟨k,hk | hk⟩ := mem_iUnion.mp hz
          · have harc := (cairns_nested_sector_gap hσ ha (d.steps j) (d.steps n)
              (hmono hjn) (hchord j) (hchord n) (fun k ↦ (hstar n k).2.2.1)
              i k ⟨z,(hstar n k).2.2.1 hk,hzβ⟩).2
            rw [hpatch k z (subset_closure hk)]
            apply cairns_geometric_patch_convex_control ((d.steps n).star k) h (hstar n k)
              C (convex_convexHull ℝ _) _ (subset_closure hk)
            intro t ht
            exact subset_convexHull ℝ _ (mem_image_of_mem τ (harc ht))
          · exact (hzold (hchord n k hk)).elim

end HolomorphicAnosov.Topology.Plane
