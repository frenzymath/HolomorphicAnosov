import HolomorphicAnosov.Topology.CairnsSuccessorCompactness
import HolomorphicAnosov.Topology.CairnsStarPatchHomeomorph
import HolomorphicAnosov.Topology.CairnsGeometricPatchConvexControl

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement
open scoped _root_.Topology

/-- The successor map is continuous on the old carrier and all closed new
stars. Anchor each star at its first retained endpoint. Source sectors and
convex target patches are bounded by the diameters of their original and
target boundary arcs. Both diameters tend to zero along distinct gaps, so
the graph-pasting theorem applies even when infinitely many patches accumulate.
Source: Cairns §4(B,C), continuity in the successive extension. -/
theorem cairns_successor_continuousOn
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (haBounded : Bornology.IsBounded a) (hs : Bornology.IsBounded s.region)
    (d : StepData σ a s) (h : range σ ≃ₜ Circle)
    (hgeo : ∀ i, StarGeometry (d.star i) h)
    (hcont : ContinuousOn s.map (closure s.region ∪ range σ))
    (hcurve : ∀ (z : ℂ) (hz : z ∈ range σ), s.map z = (h ⟨z,hz⟩ : ℂ))
    (hpatch : ∀ i z, z ∈ closure (d.star i).sourceStar →
      (d.next h).map z = (d.star i).patchMap h z) :
    ContinuousOn (d.next h).map
      ((closure s.region ∪ range σ) ∪ ⋃ i, closure (d.star i).sourceStar) := by
  classical
  let τ := fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)
  have hτ : Continuous τ := continuous_subtype_val.comp
    (h.continuous.comp (hσ.continuous.subtype_mk (fun t ↦ ⟨t,rfl⟩)))
  let r := fun i ↦ Metric.diam (σ '' (d.gap i).closedArc)
  let rt := fun i ↦ Metric.diam (τ '' (d.gap i).closedArc)
  have hold : ∀ z ∈ closure s.region ∪ range σ, (d.next h).map z = s.map z := by
    intro z hz
    change (if z ∈ closure s.region ∪ range σ then s.map z else _) = _
    exact ite_eq_left hz
  have hbounded (i) : Bornology.IsBounded (d.star i).sourceStar :=
    haBounded.subset ((hgeo i).2.2.1.trans (cairns_star_sector_geometry hσ ha (d.star i)).2.2.2)
  have hpatchcont : ∀ i, ContinuousOn (d.next h).map (closure (d.star i).sourceStar) := by
    intro i
    exact (cairns_star_patch_bijOn (d.star i) h (hgeo i)).1.congr (hpatch i)
  apply null_patch_continuousOn (closure s.region ∪ range σ)
    (hs.isCompact_closure.union (isCompact_range hσ.continuous))
    (fun i ↦ closure (d.star i).sourceStar) (fun i ↦ (hbounded i).isCompact_closure)
    (d.next h).map (hcont.congr hold) hpatchcont
    (fun i ↦ σ (d.gap i).first) (fun i ↦ Or.inl (d.gap_isGap i).1)
    (fun i ↦ r i + rt i)
  · intro i z hz
    have hfirst : (d.gap i).first ∈ (d.gap i).closedArc :=
      ⟨(d.gap i).start,⟨le_rfl,(d.gap i).start_lt_stop.le⟩,rfl⟩
    have hsrc : σ '' (d.gap i).closedArc ⊆ Metric.closedBall (σ (d.gap i).first) (r i) := by
      intro w hw
      exact Metric.dist_le_diam_of_mem
        ((isCompact_range hσ.continuous).isBounded.subset (image_subset_range _ _))
        hw (mem_image_of_mem σ hfirst)
    have hdst : ∀ t ∈ (d.gap i).closedArc, τ t ∈ Metric.closedBall (τ (d.gap i).first) (rt i) := by
      intro t ht
      exact Metric.dist_le_diam_of_mem
        ((isCompact_range hτ).isBounded.subset (image_subset_range _ _))
        (mem_image_of_mem τ ht) (mem_image_of_mem τ hfirst)
    constructor
    · have hh := cairns_star_sector_closure_subset_closedBall hσ ha haBounded
        (d.star i) _ _ hsrc (closure_mono (hgeo i).2.2.1 hz)
      exact le_trans hh (le_add_of_nonneg_right Metric.diam_nonneg)
    · rw [hpatch i z hz, hold _ (Or.inr (mem_range_self _)), hcurve _ (mem_range_self _)]
      have hh := cairns_geometric_patch_convex_control (d.star i) h (hgeo i)
        (Metric.closedBall (τ (d.gap i).first) (rt i)) (convex_closedBall _ _) hdst hz
      exact le_trans hh (le_add_of_nonneg_left Metric.diam_nonneg)
  · intro j hj
    have h₁ := CairnsCircleGap.image_diam_tendsto_zero_of_disjoint σ hσ.continuous d.gap
      (cairns_step_gap_pairwise_disjoint d) j hj
    have h₂ := CairnsCircleGap.image_diam_tendsto_zero_of_disjoint τ hτ d.gap
      (cairns_step_gap_pairwise_disjoint d) j hj
    simpa only [r, rt, Function.comp_def, add_zero] using h₁.add h₂

end HolomorphicAnosov.Topology.Plane

