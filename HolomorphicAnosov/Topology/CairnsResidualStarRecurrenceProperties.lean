import HolomorphicAnosov.Topology.CairnsResidualStarRefinement

/-!
# Monotonicity and compatibility of Cairns's literal recurrence

Source: Cairns (1951), §4(C), pp.864–865, equations (4.3)–(4.4).
-/

namespace HolomorphicAnosov.Topology.Plane

open Set CairnsRefinement

/-- The source regions, their images and their retained contact sets increase, and each
successor map preserves the preceding map on the old closed region and original curve.

Source: Cairns (1951), §4(C), pp.864–865, (4.3)–(4.4). The next region is a union
containing the old region. The first branch of the successor map keeps its value on the
old closure and curve. Consequently the image of each old point remains in the next image.
Iteration gives monotonicity; monotonicity of closure and inverse image gives the same
property for the retained contacts. These conclusions use only the recurrence equations,
without assuming any openness, continuity, cell structure or shrinking. -/
theorem cairns_residual_star_recurrence_properties
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : (range σ) ≃ₜ Circle}
    (d : Data σ a p q h) :
    Monotone (fun j ↦ (d.stages j).region) ∧
      Monotone (fun j ↦ (d.stages j).target) ∧
      Monotone (fun j ↦ (d.stages j).contacts σ) ∧
      (∀ j z, z ∈ closure (d.stages j).region ∪ range σ →
        (d.stages (j + 1)).map z = (d.stages j).map z) := by
  classical
  have hregion : ∀ j, (d.stages j).region ⊆ (d.stages (j + 1)).region := by
    intro j
    rw [d.next_eq j]
    exact subset_union_left
  have hmap : ∀ j z, z ∈ closure (d.stages j).region ∪ range σ →
      (d.stages (j + 1)).map z = (d.stages j).map z := by
    intro j z hz
    rw [d.next_eq j]
    exact ite_eq_left hz
  have hmono := monotone_nat_of_le_succ hregion
  refine ⟨hmono, monotone_nat_of_le_succ ?_, ?_, hmap⟩
  · intro j y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, hregion j hz, hmap j z (Or.inl (subset_closure hz))⟩
  · intro i j hij z hz
    exact closure_mono (hmono hij) hz

end HolomorphicAnosov.Topology.Plane

