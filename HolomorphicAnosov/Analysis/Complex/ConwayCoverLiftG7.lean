import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.Basic

open Set Filter
open scoped Topology
namespace HolomorphicAnosov

/-- A pointed continuous lift through a locally biholomorphic disk covering is
holomorphic. Source: Conway II XVI Corollary 2.6 p.114 (Theorem 1.3 and Proposition 2.1),
used in XVI Theorem 4.2 p.124. Lift on the simply connected open domain by the
covering lift theorem. At each point, the lift remains in one local inverse
sheet, on which it equals the holomorphic inverse composed with the base map. -/
theorem conway_holomorphic_disk_cover_lift_g7
    {G : Set ℂ} (hG : IsOpen G) (hc : IsSimplyConnected G)
    {lam f : ℂ → ℂ}
    (hcover : IsCoveringMapOn (fun z : {z : ℂ // ‖z‖ < 1} ↦ lam z.val)
      {w : ℂ | w ≠ 0 ∧ w ≠ 1})
    (hlocal : ∀ z : ℂ, ‖z‖ < 1 → ∃ e : OpenPartialHomeomorph ℂ ℂ,
      z ∈ e.source ∧ e.source ⊆ {w : ℂ | ‖w‖ < 1} ∧
      EqOn e lam e.source ∧ DifferentiableOn ℂ e e.source ∧
        DifferentiableOn ℂ e.symm e.target)
    (hf : DifferentiableOn ℂ f G) (ho : ∀ z ∈ G, f z ≠ 0 ∧ f z ≠ 1)
    {a w : ℂ} (ha : a ∈ G) (hw : ‖w‖ < 1) (he : lam w = f a) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g G ∧ (∀ z ∈ G, ‖g z‖ < 1) ∧
      (∀ z ∈ G, lam (g z) = f z) ∧ g a = w := by
  classical
  have := hc.simplyConnectedSpace
  have := hG.locallyPathConnectedSpace
  obtain ⟨F, ⟨hFa, hF⟩, _⟩ := hcover.existsUnique_continuousMap_lifts
    (⟨G.domRestrict f, hf.continuousOn.domRestrict⟩ : C(G, ℂ))
    (a₀ := ⟨a, ha⟩) (e₀ := ⟨w, hw⟩) he (fun z ↦ ho z z.property)
  let g : ℂ → ℂ := fun z ↦ if hz : z ∈ G then (F ⟨z, hz⟩).val else 0
  have hg (z : ℂ) (hz : z ∈ G) : g z = (F ⟨z, hz⟩).val := by simp [g, hz]
  have hgc : ContinuousOn g G := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert continuous_subtype_val.comp F.continuous using 1
    ext z
    exact hg z z.property
  have hproj (z : ℂ) (hz : z ∈ G) : lam (g z) = f z := by
    rw [hg z hz]
    exact congrFun hF ⟨z, hz⟩
  have hbound (z : ℂ) (hz : z ∈ G) : ‖g z‖ < 1 := by
    rw [hg z hz]
    exact (F ⟨z, hz⟩).property
  refine ⟨g, ?_, hbound, hproj, ?_⟩
  · intro z hz
    obtain ⟨e, hge, _, heq, _, hinv⟩ := hlocal (g z) (hbound z hz)
    have hft : f z ∈ e.target := by
      rw [← hproj z hz, ← heq hge]
      exact e.map_source hge
    have hdiff := (hinv.differentiableAt (e.open_target.mem_nhds hft)).comp z
      (hf.differentiableAt (hG.mem_nhds hz))
    apply (hdiff.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hG.mem_nhds hz,
      (hgc.continuousAt (hG.mem_nhds hz)).preimage_mem_nhds
        (e.open_source.mem_nhds hge)] with t ht hgt
    change g t = e.symm (f t)
    rw [← hproj t ht, ← heq hgt, e.left_inv hgt]
  · rw [hg a ha]
    exact congrArg Subtype.val hFa

end HolomorphicAnosov
