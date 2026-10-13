import Mathlib.Topology.Connected.Basic

/-! DAG node: `topo.two_components_exhaust_local_cover_g10`. -/

open Set
namespace HolomorphicAnosov

/-- If two open components cover a neighborhood of a relatively closed cut in
a connected open region, they exhaust its complement. Agent expansion of Cairns
(1951), Lemma 3.1(C). Adjoin the cut to the two components. The resulting set is
open by the neighborhood hypothesis and relatively closed by the component
frontier condition and relative closedness of the cut. It meets the connected
region, so it is the whole region. -/
theorem two_components_exhaust_of_local_cover
    {X : Type*} [TopologicalSpace X] {A S B₁ B₂ : Set X}
    (hA : IsPreconnected A)
    (h₁ : IsOpen B₁) (h₂ : IsOpen B₂)
    (h₁sub : B₁ ⊆ A \ S) (h₂sub : B₂ ⊆ A \ S)
    (hne : B₁.Nonempty) (hSclosed : closure S ∩ A ⊆ S)
    (hf₁ : frontier B₁ ⊆ (A \ S)ᶜ) (hf₂ : frontier B₂ ⊆ (A \ S)ᶜ)
    (hlocal : ∀ z ∈ S, B₁ ∪ B₂ ∪ S ∈ nhds z) :
    A \ S = B₁ ∪ B₂ := by
  let W := B₁ ∪ B₂ ∪ S
  have hW : IsOpen W := by
    apply isOpen_iff_mem_nhds.mpr
    rintro z ((hz | hz) | hz)
    · exact Filter.mem_of_superset (h₁.mem_nhds hz) (fun _ h ↦ Or.inl (Or.inl h))
    · exact Filter.mem_of_superset (h₂.mem_nhds hz) (fun _ h ↦ Or.inl (Or.inr h))
    · exact hlocal z hz
  have hclosure : closure W ∩ A ⊆ W := by
    rintro z ⟨hzw, hza⟩
    rw [show W = B₁ ∪ B₂ ∪ S from rfl, closure_union, closure_union] at hzw
    rcases hzw with (hz | hz) | hz
    · by_cases hz₁ : z ∈ B₁
      · exact Or.inl (Or.inl hz₁)
      · right
        by_contra hzS
        exact hf₁ (h₁.frontier_eq.symm ▸ ⟨hz, hz₁⟩) ⟨hza, hzS⟩
    · by_cases hz₂ : z ∈ B₂
      · exact Or.inl (Or.inr hz₂)
      · right
        by_contra hzS
        exact hf₂ (h₂.frontier_eq.symm ▸ ⟨hz, hz₂⟩) ⟨hza, hzS⟩
    · exact Or.inr (hSclosed ⟨hz, hza⟩)
  obtain ⟨x, hx⟩ := hne
  have hAW := hA.subset_of_closure_inter_subset hW
    ⟨x, (h₁sub hx).1, Or.inl (Or.inl hx)⟩ hclosure
  apply subset_antisymm
  · intro z hz
    exact (hAW hz.1).resolve_right hz.2
  · exact union_subset h₁sub h₂sub

end HolomorphicAnosov

