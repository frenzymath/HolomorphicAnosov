import HolomorphicAnosov.Topology.CairnsTargetSectorSelection
import HolomorphicAnosov.Topology.CairnsTargetSectorHull
import HolomorphicAnosov.Topology.CairnsGapHullSeparation
import HolomorphicAnosov.Topology.CairnsSuccessorCompactness

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- The target sectors for the actual source gap labels are pairwise disjoint.
Choose the outside component independently for each label. Its closure is the
corresponding arc hull; two distinct such hulls overlap only in the old target
closure, which both open outside sectors avoid. Source: Cairns §4(C). -/
theorem cairns_target_sector_family
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ) (hab : Bornology.IsBounded a)
    (h : range σ ≃ₜ Circle) (hs : StageGeometry σ a h s) (d : StepData σ a s) :
    let τ := fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)
    ∃ b : ∀ i, StarChoice τ (Metric.ball (0 : ℂ) 1) (d.gap i),
      (∀ i, Disjoint (b i).sector s.target ∧
        (b i).sector.Nonempty ∧ IsOpen (b i).sector ∧ IsConnected (b i).sector ∧
        (∃ x ∈ Metric.ball (0 : ℂ) 1 \ closure s.target,
          connectedComponentIn (Metric.ball (0 : ℂ) 1 \ closure s.target) x = (b i).sector) ∧
        (∀ z r, τ '' (d.gap i).closedArc ⊆ Metric.closedBall z r →
          closure (b i).sector ⊆ Metric.closedBall z r) ∧
        closure (b i).sector = convexHull ℝ (τ '' (d.gap i).closedArc) ∧
        Convex ℝ (b i).sector) ∧
      Pairwise (fun i j ↦ Disjoint (b i).sector (b j).sector) := by
  classical
  intro τ
  choose b hb using fun i ↦ cairns_target_sector_selection hσ hab h hs (d.gap i) (d.gap_isGap i)
  obtain ⟨hτ,hτrange,hcomponent⟩ := cairns_target_boundary_geometry hσ h
  have hnorm : ∀ t, ‖τ t‖ = 1 := fun t ↦ Circle.norm_coe _
  have hsurj : ∀ z : ℂ, ‖z‖ = 1 → ∃ t, τ t = z := by
    intro z hz
    let e : Circle ≃ₜ Circle := hσ.toHomeomorph.trans h
    let zc : Circle := ⟨z,mem_sphere_zero_iff_norm.mpr hz⟩
    exact ⟨e.symm zc,congrArg Subtype.val (e.apply_symm_apply zc)⟩
  have hh := fun i ↦ cairns_target_sector_hull τ hτ hnorm hcomponent (d.gap i) (b i)
  refine ⟨b,(fun i ↦ ⟨(hb i).1,(hb i).2.1,(hb i).2.2.1,(hb i).2.2.2.1,
    (hb i).2.2.2.2.1,(hb i).2.2.2.2.2,(hh i).2⟩),?_⟩
  intro i j hij
  apply disjoint_left.mpr
  intro z hzi hzj
  have hover := cairns_disjoint_gap_hulls_overlap_in_contact_hull τ hτ.continuous
    hτ.injective hnorm hsurj (s.contacts σ) (d.gap i) (d.gap j)
    (d.gap_isGap i) (d.gap_isGap j) (cairns_step_gap_pairwise_disjoint d hij)
  have hzcl : z ∈ closure s.target := by
    rw [hs.target_closure]
    exact hover ⟨(hh i).2.1 ▸ subset_closure hzi,(hh j).2.1 ▸ subset_closure hzj⟩
  exact disjoint_left.mp ((hb i).1.closure_right (hb i).2.2.1) hzi hzcl

end HolomorphicAnosov.Topology.Plane

