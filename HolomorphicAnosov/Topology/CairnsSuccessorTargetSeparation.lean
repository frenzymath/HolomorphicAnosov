import HolomorphicAnosov.Topology.CairnsStarTargetConvexity
import HolomorphicAnosov.Topology.CairnsGapHullSeparation
import HolomorphicAnosov.Topology.CairnsSuccessorCompactness

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- Each new closed target star meets the old contact hull only in its base,
and two distinct new closed stars meet only in that old hull. Their contacts
lie in the corresponding residual closed arcs; strict supporting chord
functionals separate these arcs. The proof accommodates any orientation of
the prescribed boundary homeomorphism. Source: Cairns §4(C). -/
theorem cairns_successor_target_separation
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (hσ : Topology.IsEmbedding σ) (d : StepData σ a s) (h : range σ ≃ₜ Circle)
    (hgeo : ∀ i, StarGeometry (d.star i) h)
    (hold : closure s.target = convexHull ℝ
      ((fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)) '' s.contacts σ)) :
    (∀ i, closure ((d.star i).targetStar h) ∩ closure s.target =
      segment ℝ (h ⟨σ (d.gap i).first,⟨(d.gap i).first,rfl⟩⟩ : ℂ)
        (h ⟨σ (d.gap i).last,⟨(d.gap i).last,rfl⟩⟩ : ℂ)) ∧
    (∀ i j, i ≠ j → closure ((d.star i).targetStar h) ∩
      closure ((d.star j).targetStar h) ⊆ closure s.target) := by
  let τ := fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)
  let e : Circle ≃ₜ Circle := hσ.toHomeomorph.trans h
  have hτ : Continuous τ := continuous_subtype_val.comp e.continuous
  have hτinj : Function.Injective τ := fun s t he ↦ e.injective (Subtype.ext he)
  have hτnorm : ∀ t, ‖τ t‖ = 1 := fun t ↦ Circle.norm_coe _
  have hτsurj : ∀ z : ℂ, ‖z‖ = 1 → ∃ t, τ t = z := by
    intro z hz
    let zc : Circle := ⟨z,mem_sphere_zero_iff_norm.mpr hz⟩
    exact ⟨e.symm zc,congrArg Subtype.val (e.apply_symm_apply zc)⟩
  let T := fun i ↦ σ ⁻¹' ((d.star i).front ∩ range σ)
  have hT : ∀ i, T i ⊆ (d.gap i).closedArc := by
    intro i t ht
    have hCsub : (d.star i).front ∩ range σ ⊆ σ '' range (d.gap i).parameter :=
      (hgeo i).2.2.2.2.2.2.2.2.2.1
    obtain ⟨u,hu,he⟩ := hCsub ht
    have hut : u = t := hσ.injective he
    rw [← hut,← (CairnsCircleGap.parameter_embedding_range (d.gap i)).2.1]
    exact hu
  have hcl : ∀ i, closure ((d.star i).targetStar h) = convexHull ℝ (τ '' T i) :=
    fun i ↦ cairns_geometric_star_target_closure hσ (d.star i) h (hgeo i)
  constructor
  · intro i
    rw [hcl,hold]
    exact cairns_gap_hull_inter_contact_hull τ hτ hτinj hτnorm hτsurj
      (s.contacts σ) (d.gap i) (d.gap_isGap i) (T i) (hT i)
      (hgeo i).2.2.2.2.2.2.2.2.2.2.1 (hgeo i).2.2.2.2.2.2.2.2.2.2.2.1
  · intro i j hij z hz
    rw [hold]
    apply cairns_disjoint_gap_hulls_overlap_in_contact_hull τ hτ hτinj hτnorm hτsurj
      (s.contacts σ) (d.gap i) (d.gap j) (d.gap_isGap i) (d.gap_isGap j)
      (cairns_step_gap_pairwise_disjoint d hij)
    rw [hcl i,hcl j] at hz
    exact ⟨convexHull_mono (image_mono (hT i)) hz.1,
      convexHull_mono (image_mono (hT j)) hz.2⟩

end HolomorphicAnosov.Topology.Plane

