import HolomorphicAnosov.Topology.CairnsTwoDiskCells
import HolomorphicAnosov.Topology.DiskChartBoundaryAdjustment

namespace HolomorphicAnosov.Topology
open Set Metric

/-- Two disk cells sharing exactly a proper frontier chord have an open union
when the open chord is inserted. Adjust each disk chart to the boundary
parametrization required by the half-disk gluing theorem, and use the affine
chord embedding to identify the common seam. Source: Cairns §4(B,C). -/
theorem cairns_disk_cells_open_along_chord
    (U V : Set ℂ) (p q : ℂ) (hpq : p ≠ q)
    (hcell : ∀ W ∈ ({U,V} : Set (Set ℂ)),
      ∃ G : closure W ≃ₜ closedBall (0 : ℂ) 1,
        G '' {z : closure W | (z : ℂ) ∈ W} =
          {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ ball (0 : ℂ) 1} ∧
        G '' {z : closure W | (z : ℂ) ∈ frontier W} =
          {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ sphere (0 : ℂ) 1})
    (hBU : segment ℝ p q ⊆ frontier U) (hBV : segment ℝ p q ⊆ frontier V)
    (hpU : segment ℝ p q ≠ frontier U) (hpV : segment ℝ p q ≠ frontier V)
    (hinter : closure U ∩ closure V = segment ℝ p q) :
    IsOpen (U ∪ V ∪ openSegment ℝ p q) := by
  have hcellAmbient (W : Set ℂ) (hW : W ∈ ({U,V} : Set (Set ℂ))) :
      ∃ H : closure W ≃ₜ closedBall (0 : ℂ) 1,
        H '' {z | (z : ℂ) ∈ W} = {w | (w : ℂ) ∈ ball (0 : ℂ) 1} ∧
        H '' {z | (z : ℂ) ∈ frontier W} = {w | (w : ℂ) ∈ sphere (0 : ℂ) 1} := by
    obtain ⟨G,hi,hf⟩ := hcell W hW
    refine ⟨G,?_,?_⟩
    · have hh := congrArg (Set.image (Subtype.val : closedBall (0 : ℂ) 1 → ℂ)) hi
      change Subtype.val '' G '' {z : closure W | (z : ℂ) ∈ W} = ball (0 : ℂ) 1
      rw [hh]
      exact Set.image_preimage_eq_of_subset (by simpa only [Subtype.range_coe] using
        (ball_subset_closedBall : ball (0 : ℂ) 1 ⊆ closedBall 0 1))
    · have hh := congrArg (Set.image (Subtype.val : closedBall (0 : ℂ) 1 → ℂ)) hf
      change Subtype.val '' G '' {z : closure W | (z : ℂ) ∈ frontier W} = sphere (0 : ℂ) 1
      rw [hh]
      exact Set.image_preimage_eq_of_subset (by simpa only [Subtype.range_coe] using
        (sphere_subset_closedBall : sphere (0 : ℂ) 1 ⊆ closedBall 0 1))
  have hext (W : Set ℂ) (hW : W ∈ ({U,V} : Set (Set ℂ)))
      (e : frontier W ≃ₜ sphere (0 : ℂ) 1) :
      ∃ H : closure W ≃ₜ closedBall (0 : ℂ) 1,
        ∀ z : closure W, ∀ hz : (z : ℂ) ∈ frontier W,
          (H z : ℂ) = (e ⟨z,hz⟩ : ℂ) := by
    obtain ⟨G,hi,hf⟩ := hcell W hW
    obtain ⟨G',hGi',hGe⟩ := disk_chart_boundary_adjustment (closure W) (frontier W) W
      frontier_subset_closure G hi hf e
    exact ⟨G',hGe⟩
  have harc : ∃ b : unitInterval → ℂ,
      Topology.IsEmbedding b ∧ range b = segment ℝ p q ∧ b 0 = p ∧ b 1 = q := by
    let b : unitInterval → ℂ := fun t ↦ AffineMap.lineMap p q (t : ℝ)
    have hbc : Continuous b := by fun_prop
    have hbi : Function.Injective b := by
      intro s t he
      exact Subtype.ext (AffineMap.lineMap_injective ℝ hpq he)
    refine ⟨b,hbc.isClosedEmbedding hbi |>.isEmbedding,?_,by simp [b],by simp [b]⟩
    rw [segment_eq_image_lineMap]
    exact Set.range_comp _ _ |>.trans (by rw [Subtype.range_coe])
  have hfrontinter : frontier U ∩ frontier V = segment ℝ p q := by
    apply Subset.antisymm
    · intro z hz
      exact hinter ▸ ⟨frontier_subset_closure hz.1,frontier_subset_closure hz.2⟩
    · exact fun z hz ↦ ⟨hBU hz,hBV hz⟩
  have hseam : segment ℝ p q \ {p,q} = openSegment ℝ p q := by
    ext z
    constructor
    · intro hz
      exact mem_openSegment_of_ne_left_right (fun he ↦ hz.2 (Or.inl he.symm))
        (fun he ↦ hz.2 (Or.inr he.symm)) hz.1
    · intro hz
      refine ⟨openSegment_subset_segment ℝ _ _ hz,?_⟩
      rintro (rfl | rfl)
      · exact hpq (left_mem_openSegment_iff.mp hz)
      · exact hpq (right_mem_openSegment_iff.mp hz)
  have hh := (cairns_two_disk_cells U V (segment ℝ p q) p q
    (hcellAmbient U (Or.inl rfl)) (hcellAmbient V (Or.inr rfl))
    (hext U (Or.inl rfl)) (hext V (Or.inr rfl)) hpq harc
    ⟨hBU,hpU⟩ ⟨hBV,hpV⟩ hfrontinter hinter).1
  simpa only [hseam] using hh

end HolomorphicAnosov.Topology

