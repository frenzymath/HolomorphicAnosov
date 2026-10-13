import HolomorphicAnosov.Topology.CairnsOppositeCellsBoundaryCycle
import HolomorphicAnosov.Topology.CairnsDiskCellRelativeChart
import HolomorphicAnosov.Topology.AmbientCircleBoundedCell
import HolomorphicAnosov.Topology.SegmentProperAmbientCircleArc
import HolomorphicAnosov.Topology.DiskChartTwoRegions

namespace HolomorphicAnosov
open Set Metric

/-- Boundary polygon stitching and the two-region separation output in Cairns preliminary 2(A,B).
Source: Cairns preliminary 2(B), p.860, and Hatcher Proposition 2B.1 and Theorem
2B.3, pp.169–172. Parametrize the seam as a proper circle arc, glue the two
closed-disk charts using the existing relative gluing theorem, then use disk
nonseparation and invariance of domain to identify the two regions and their
frontiers. The separate cycle theorem supplies the finite polygon boundary. -/
theorem cairns_opposite_cells_boundary_separation
    {n₁ n₂ : ℕ} (q₁ : Polygon ℂ (n₁ + 3)) (q₂ : Polygon ℂ (n₂ + 3))
    (hq₁_vertices : Function.Injective q₁.vertices)
    (hq₁_edges : q₁.HasNondegenerateEdges)
    (hq₁_simple : ∀ i j : Fin (n₁ + 3), i ≠ j →
      q₁.edgeSet ℝ i ∩ q₁.edgeSet ℝ j =
        ({q₁ i, q₁ (finRotate (n₁ + 3) i)} : Set ℂ) ∩
        {q₁ j, q₁ (finRotate (n₁ + 3) j)})
    (hq₂_vertices : Function.Injective q₂.vertices)
    (hq₂_edges : q₂.HasNondegenerateEdges)
    (hq₂_simple : ∀ i j : Fin (n₂ + 3), i ≠ j →
      q₂.edgeSet ℝ i ∩ q₂.edgeSet ℝ j =
        ({q₂ i, q₂ (finRotate (n₂ + 3) i)} : Set ℂ) ∩
        {q₂ j, q₂ (finRotate (n₂ + 3) j)})
    (hq₁_ambient : ∃ F : ℂ ≃ₜ ℂ, F '' q₁.boundary ℝ = Metric.sphere (0 : ℂ) 1)
    (hq₂_ambient : ∃ F : ℂ ≃ₜ ℂ, F '' q₂.boundary ℝ = Metric.sphere (0 : ℂ) 1)
    (u₁ u₂ : ℂ) (hu₁ : u₁ ∉ q₁.boundary ℝ) (hu₂ : u₂ ∉ q₂.boundary ℝ)
    (C₁ C₂ : Set ℂ)
    (hC₁ : C₁ = connectedComponentIn (q₁.boundary ℝ)ᶜ u₁)
    (hC₂ : C₂ = connectedComponentIn (q₂.boundary ℝ)ᶜ u₂)
    (hC₁_bounded : Bornology.IsBounded C₁) (hC₂_bounded : Bornology.IsBounded C₂)
    (a b : ℂ) (hab : a ≠ b)
    (hq_inter : q₁.boundary ℝ ∩ q₂.boundary ℝ = segment ℝ a b)
    (hD_inter : closure C₁ ∩ closure C₂ = segment ℝ a b)
    (_h_opposite : ∀ x ∈ openSegment ℝ a b, ∃ ε : ℝ, 0 < ε ∧
      ∃ ν : ℂ, ‖ν‖ = 1 ∧ ((b - a) / ν).re = 0 ∧
        Metric.ball x ε ∩ C₁ = {z : ℂ | z ∈ Metric.ball x ε ∧ 0 < ((z - x) / ν).re} ∧
        Metric.ball x ε ∩ C₂ = {z : ℂ | z ∈ Metric.ball x ε ∧ ((z - x) / ν).re < 0})
    (hlocal : IsOpen C₁ ∧ IsOpen C₂ ∧
      IsCompact (closure C₁ ∪ closure C₂) ∧
      IsConnected (closure C₁ ∪ closure C₂) ∧
      closure (interior (closure C₁ ∪ closure C₂)) = closure C₁ ∪ closure C₂ ∧
      (interior (closure C₁ ∪ closure C₂)).Nonempty ∧
      openSegment ℝ a b ⊆ interior (closure C₁ ∪ closure C₂)) :
    let p : Set ℂ := (q₁.boundary ℝ ∪ q₂.boundary ℝ) \ openSegment ℝ a b
    let D : Set ℂ := closure C₁ ∪ closure C₂
    (∃ (n : ℕ) (q : Polygon ℂ (n + 3)),
      Function.Injective q.vertices ∧ q.HasNondegenerateEdges ∧
      (∀ i j : Fin (n + 3), i ≠ j →
        q.edgeSet ℝ i ∩ q.edgeSet ℝ j =
          ({q i, q (finRotate (n + 3) i)} : Set ℂ) ∩
          {q j, q (finRotate (n + 3) j)}) ∧ q.boundary ℝ = p) ∧
    (∃ B E : Set ℂ,
      (fun z : ℂ ↦ connectedComponentIn pᶜ z) '' pᶜ = {B, E} ∧
      IsConnected B ∧ IsConnected E ∧ IsOpen B ∧ IsOpen E ∧
      Bornology.IsBounded B ∧ ¬ Bornology.IsBounded E ∧
      closure B = D ∧ frontier B = p ∧ frontier E = p):= by
  dsimp only
  have hpoly := cairns_opposite_cells_boundary_cycle q₁ q₂
    hq₁_vertices hq₁_edges hq₁_simple hq₂_vertices hq₂_edges hq₂_simple a b hab hq_inter
  refine ⟨hpoly, ?_⟩
  obtain ⟨F₁, hF₁⟩ := hq₁_ambient
  obtain ⟨F₂, hF₂⟩ := hq₂_ambient
  obtain ⟨hc₁, hcell₁, hext₁⟩ := ambientCircle_bounded_cell
    (q₁.boundary ℝ) C₁ F₁ hF₁ u₁ hu₁ hC₁ hC₁_bounded
  obtain ⟨hc₂, hcell₂, hext₂⟩ := ambientCircle_bounded_cell
    (q₂.boundary ℝ) C₂ F₂ hF₂ u₂ hu₂ hC₂ hC₂_bounded
  have hs₁ : segment ℝ a b ⊆ q₁.boundary ℝ := by
    rw [← hq_inter]; exact inter_subset_left
  have hs₂ : segment ℝ a b ⊆ q₂.boundary ℝ := by
    rw [← hq_inter]; exact inter_subset_right
  have flat {U c : Set ℂ}
      (h : ∃ H : closure U ≃ₜ closedBall (0 : ℂ) 1,
        H '' {z | (z : ℂ) ∈ U} = {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ ball (0 : ℂ) 1} ∧
        H '' {z | (z : ℂ) ∈ c} = {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ sphere (0 : ℂ) 1}) :
      ∃ H : closure U ≃ₜ closedBall (0 : ℂ) 1,
        Subtype.val '' (H '' {z | (z : ℂ) ∈ U}) = ball (0 : ℂ) 1 ∧
        Subtype.val '' (H '' {z | (z : ℂ) ∈ c}) = sphere (0 : ℂ) 1 := by
    obtain ⟨H, hR, hC⟩ := h
    refine ⟨H, ?_, ?_⟩
    · rw [hR]
      exact (Subtype.image_preimage_coe _ _).trans (inter_eq_right.mpr ball_subset_closedBall)
    · rw [hC]
      exact (Subtype.image_preimage_coe _ _).trans (inter_eq_right.mpr sphere_subset_closedBall)
  obtain ⟨H, hR, hC⟩ := Topology.cairns_disk_cell_relative_chart C₁ C₂
    (q₁.boundary ℝ) (q₂.boundary ℝ) (segment ℝ a b) a b hc₁ hc₂
    (flat hcell₁) (flat hcell₂) hext₁ hext₂ hab (segment_embedded_arc a b hab)
    ⟨hs₁, segment_ne_ambient_circle _ F₁ hF₁ a b hab hs₁⟩
    ⟨hs₂, segment_ne_ambient_circle _ F₂ hF₂ a b hab hs₂⟩
    hq_inter hD_inter (isClosed_closure.union isClosed_closure)
  have hseg : segment ℝ a b \ {a, b} = openSegment ℝ a b := by
    ext z
    simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · rintro ⟨hz, hza, hzb⟩
      exact mem_openSegment_of_ne_left_right (Ne.symm hza) (Ne.symm hzb) hz
    · intro hz
      exact ⟨openSegment_subset_segment ℝ a b hz,
        (fun he ↦ hab (left_mem_openSegment_iff.mp (he ▸ hz))),
        (fun he ↦ hab (right_mem_openSegment_iff.mp (he ▸ hz)))⟩
  rw [hseg] at hR hC
  let K : Set ℂ := closure C₁ ∪ closure C₂
  let R : Set ℂ := C₁ ∪ C₂ ∪ openSegment ℝ a b
  let C : Set ℂ := (q₁.boundary ℝ ∪ q₂.boundary ℝ) \ openSegment ℝ a b
  have hRK : R ⊆ K := by
    apply union_subset
    · exact union_subset_union subset_closure subset_closure
    · exact hlocal.2.2.2.2.2.2.trans interior_subset
  have hCK : C ⊆ K :=
    sdiff_subset.trans (union_subset_union hc₁ hc₂)
  have hout := diskChart_two_regions K R C hlocal.2.2.1
    hlocal.2.2.2.2.1 hlocal.2.2.2.2.2.1 hRK hCK H hR hC
  exact ⟨interior K, Kᶜ, hout⟩
end HolomorphicAnosov

