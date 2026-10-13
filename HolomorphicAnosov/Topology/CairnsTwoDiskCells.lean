import HolomorphicAnosov.Topology.CairnsDiskCellRelativeChart
import HolomorphicAnosov.Topology.DiskChartOpenInteriorBoundary
import HolomorphicAnosov.Topology.CairnsSeamSubsetClosure

namespace HolomorphicAnosov.Topology
open Set Metric

/-- Gluing two closed disk cells along a proper common boundary arc gives an
open disk region with the expected ambient frontier. This is the finite gluing
step of Cairns §4(B,D). The relative chart is supplied by the existing half-disk
pasting theorem. The independent planar open-image theorem gives ambient
openness. Both old open cells are dense in their closures, so the new closure
is their union; the chart then identifies its complement of the open region
with the two outer boundary arcs. No exterior-component hypothesis is needed. -/
theorem cairns_two_disk_cells
    (U V B : Set ℂ) (p q : ℂ)
    (hcellU : ∃ H : closure U ≃ₜ closedBall (0 : ℂ) 1,
      H '' {z | (z : ℂ) ∈ U} = {w | (w : ℂ) ∈ ball (0 : ℂ) 1} ∧
      H '' {z | (z : ℂ) ∈ frontier U} = {w | (w : ℂ) ∈ sphere (0 : ℂ) 1})
    (hcellV : ∃ H : closure V ≃ₜ closedBall (0 : ℂ) 1,
      H '' {z | (z : ℂ) ∈ V} = {w | (w : ℂ) ∈ ball (0 : ℂ) 1} ∧
      H '' {z | (z : ℂ) ∈ frontier V} = {w | (w : ℂ) ∈ sphere (0 : ℂ) 1})
    (hextU : ∀ h : frontier U ≃ₜ sphere (0 : ℂ) 1,
      ∃ H : closure U ≃ₜ closedBall (0 : ℂ) 1,
        ∀ z : closure U, ∀ hz : (z : ℂ) ∈ frontier U,
          (H z : ℂ) = (h ⟨z,hz⟩ : ℂ))
    (hextV : ∀ h : frontier V ≃ₜ sphere (0 : ℂ) 1,
      ∃ H : closure V ≃ₜ closedBall (0 : ℂ) 1,
        ∀ z : closure V, ∀ hz : (z : ℂ) ∈ frontier V,
          (H z : ℂ) = (h ⟨z,hz⟩ : ℂ))
    (hpq : p ≠ q)
    (harc : ∃ b : unitInterval → ℂ,
      Topology.IsEmbedding b ∧ range b = B ∧ b 0 = p ∧ b 1 = q)
    (hproperU : B ⊆ frontier U ∧ B ≠ frontier U)
    (hproperV : B ⊆ frontier V ∧ B ≠ frontier V)
    (hboundaryIntersection : frontier U ∩ frontier V = B)
    (hcellIntersection : closure U ∩ closure V = B) :
    let R := U ∪ V ∪ (B \ {p,q})
    let C := (frontier U ∪ frontier V) \ (B \ {p,q})
    IsOpen R ∧ closure R = closure U ∪ closure V ∧ frontier R = C ∧
      ∃ H : ↥(closure U ∪ closure V) ≃ₜ closedBall (0 : ℂ) 1,
        H '' {z | (z : ℂ) ∈ R} =
          {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ ball (0 : ℂ) 1} ∧
        H '' {z | (z : ℂ) ∈ C} =
          {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ sphere (0 : ℂ) 1} := by
  intro R C
  let K := closure U ∪ closure V
  have hRK : R ⊆ K := by
    rintro z ((hz | hz) | hz)
    · exact Or.inl (subset_closure hz)
    · exact Or.inr (subset_closure hz)
    · exact Or.inl (frontier_subset_closure (hproperU.1 hz.1))
  have hCK : C ⊆ K := by
    intro z hz
    exact hz.1.elim (fun hz ↦ Or.inl (frontier_subset_closure hz))
      (fun hz ↦ Or.inr (frontier_subset_closure hz))
  obtain ⟨H,hR,hC⟩ := cairns_disk_cell_relative_chart U V (frontier U) (frontier V) B p q
    frontier_subset_closure frontier_subset_closure hcellU hcellV hextU hextV hpq harc
    hproperU hproperV hboundaryIntersection hcellIntersection
    (isClosed_closure.union isClosed_closure)
  obtain ⟨hopen,hcircle⟩ := disk_chart_open_interior_boundary K R C hRK hCK H hR hC
  have hclosure : closure R = K := by
    apply Subset.antisymm
    · exact closure_minimal hRK (isClosed_closure.union isClosed_closure)
    · exact union_subset (closure_mono (fun z hz ↦ Or.inl (Or.inl hz)))
        (closure_mono (fun z hz ↦ Or.inl (Or.inr hz)))
  have hRiff (x : K) : (x : ℂ) ∈ R ↔ (H x : ℂ) ∈ ball (0 : ℂ) 1 := by
    change x ∈ {x : K | (x : ℂ) ∈ R} ↔ H x ∈
      {y : closedBall (0 : ℂ) 1 | (y : ℂ) ∈ ball (0 : ℂ) 1}
    rw [← hR]
    exact H.injective.mem_set_image.symm
  have hCiff (x : K) : (x : ℂ) ∈ C ↔ (H x : ℂ) ∈ sphere (0 : ℂ) 1 := by
    change x ∈ {x : K | (x : ℂ) ∈ C} ↔ H x ∈
      {y : closedBall (0 : ℂ) 1 | (y : ℂ) ∈ sphere (0 : ℂ) 1}
    rw [← hC]
    exact H.injective.mem_set_image.symm
  have hfront : frontier R = C := by
    rw [hopen.frontier_eq,hclosure]
    ext x
    constructor
    · intro hx
      apply (hCiff ⟨x,hx.1⟩).mpr
      have hn : ‖(H ⟨x,hx.1⟩ : ℂ)‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using (H ⟨x,hx.1⟩).property
      have hnot : ¬ ‖(H ⟨x,hx.1⟩ : ℂ)‖ < 1 := by
        intro hh
        exact hx.2 ((hRiff ⟨x,hx.1⟩).mpr (by simpa using hh))
      simpa using le_antisymm hn (le_of_not_gt hnot)
    · intro hx
      refine ⟨hCK hx,?_⟩
      intro hr
      exact Set.disjoint_left.mp sphere_disjoint_ball
        ((hCiff ⟨x,hCK hx⟩).mp hx) ((hRiff ⟨x,hCK hx⟩).mp hr)
  exact ⟨hopen,hclosure,hfront,H,hR,hC⟩

end HolomorphicAnosov.Topology
