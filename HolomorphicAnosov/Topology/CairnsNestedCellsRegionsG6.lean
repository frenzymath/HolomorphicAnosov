import Mathlib.Topology.Connected.Basic

open Set
namespace HolomorphicAnosov

/-- If two cells are nested and share an arc, their difference and the union of
the inner cell, outer exterior and open seam form two regions of the outer cycle.
Source: Cairns (1951), Theorem 2.1, non-nesting step. Off the seam each outer
boundary arc lies in the other curve's appropriate open region. The common
frontier property and density of those arcs give both frontiers. The explicit
seam neighborhood hypothesis supplies openness at the points added to the union. -/
theorem cairns_nested_cells_regions_g6 {X : Type*} [TopologicalSpace X]
    {C₁ E₁ c₁ C₂ E₂ c₂ D d : Set X}
    (hC₁ : IsOpen C₁) (hE₁ : IsOpen E₁) (hC₂ : IsOpen C₂) (hE₂ : IsOpen E₂)
    (hd₁ : Disjoint C₁ E₁) (hd₂ : Disjoint C₂ E₂)
    (hc₁ : C₁ ∪ E₁ = c₁ᶜ) (hc₂ : C₂ ∪ E₂ = c₂ᶜ)
    (hcl₁ : closure C₁ = C₁ ∪ c₁) (hcl₂ : c₂ ⊆ closure C₂)
    (hecl₁ : c₁ ⊆ closure E₁) (hecl₂ : c₂ ⊆ closure E₂)
    (hi : c₁ ∩ c₂ = D) (hdD : d ⊆ D)
    (harc₁ : closure (c₁ \ D) = c₁ \ d)
    (harc₂ : closure (c₂ \ D) = c₂ \ d)
    (hsub : C₂ ⊆ C₁)
    (hseam : ∀ x ∈ d, C₂ ∪ E₁ ∪ d ∈ nhds x) :
    IsOpen (C₁ ∩ E₂) ∧ IsOpen (C₂ ∪ E₁ ∪ d) ∧
      Disjoint (C₁ ∩ E₂) (C₂ ∪ E₁ ∪ d) ∧
      (C₁ ∩ E₂) ∪ (C₂ ∪ E₁ ∪ d) = ((c₁ ∪ c₂) \ d)ᶜ ∧
      (c₁ ∪ c₂) \ d ⊆ closure (C₁ ∩ E₂) ∧
      (c₁ ∪ c₂) \ d ⊆ closure (C₂ ∪ E₁ ∪ d) := by
  have hCd₁ : Disjoint C₁ c₁ := by
    apply disjoint_left.mpr
    intro x hx hxc
    exact (show x ∈ c₁ᶜ from hc₁ ▸ Or.inl hx) hxc
  have hEd₁ : Disjoint E₁ c₁ := by
    apply disjoint_left.mpr
    intro x hx hxc
    exact (show x ∈ c₁ᶜ from hc₁ ▸ Or.inr hx) hxc
  have hCd₂ : Disjoint C₂ c₂ := by
    apply disjoint_left.mpr
    intro x hx hxc
    exact (show x ∈ c₂ᶜ from hc₂ ▸ Or.inl hx) hxc
  have hEd₂ : Disjoint E₂ c₂ := by
    apply disjoint_left.mpr
    intro x hx hxc
    exact (show x ∈ c₂ᶜ from hc₂ ▸ Or.inr hx) hxc
  have hc₂cl : c₂ ⊆ C₁ ∪ c₁ := by
    rw [← hcl₁]
    exact hcl₂.trans (closure_mono hsub)
  have ha₁ : c₁ \ D ⊆ E₂ := by
    rintro x ⟨hx₁,hxD⟩
    have hx₂ : x ∉ c₂ := fun hx₂ ↦ hxD (hi ▸ ⟨hx₁,hx₂⟩)
    have hx : x ∈ C₂ ∪ E₂ := hc₂.symm ▸ hx₂
    exact hx.elim (fun h ↦ (disjoint_left.mp hCd₁ (hsub h) hx₁).elim) id
  have ha₂ : c₂ \ D ⊆ C₁ := by
    rintro x ⟨hx₂,hxD⟩
    exact (hc₂cl hx₂).elim id (fun h ↦ (hxD (hi ▸ ⟨h,hx₂⟩)).elim)
  have hacc {A B S : Set X} (hB : IsOpen B) (hS : S ⊆ closure A)
      (hSB : S ⊆ B) : S ⊆ closure (A ∩ B) := by
    intro x hx
    apply mem_closure_iff.mpr
    intro U hU hxU
    obtain ⟨y,hyU,hyA⟩ := mem_closure_iff.mp (hS hx) (U ∩ B)
      (hU.inter hB) ⟨hxU,hSB hx⟩
    exact ⟨y,hyU.1,hyA,hyU.2⟩
  have hfront₁ : c₁ \ D ⊆ closure (C₁ ∩ E₂) :=
    hacc hE₂ (fun x hx ↦ hcl₁.symm ▸ Or.inr hx.1) ha₁
  have hfront₂ : c₂ \ D ⊆ closure (C₁ ∩ E₂) := by
    rw [inter_comm]
    exact hacc hC₁ (fun x hx ↦ hecl₂ hx.1) ha₂
  have hfront : (c₁ ∪ c₂) \ d ⊆ closure (C₁ ∩ E₂) := by
    rintro x ⟨hx,hxd⟩
    rcases hx with hx | hx
    · exact closure_minimal hfront₁ isClosed_closure (harc₁.symm ▸ ⟨hx,hxd⟩)
    · exact closure_minimal hfront₂ isClosed_closure (harc₂.symm ▸ ⟨hx,hxd⟩)
  refine ⟨hC₁.inter hE₂, ?_, ?_, ?_, hfront, ?_⟩
  · apply isOpen_iff_mem_nhds.mpr
    intro x hx
    rcases hx with (hx | hx) | hx
    · exact Filter.mem_of_superset (hC₂.mem_nhds hx) (fun y hy ↦ Or.inl (Or.inl hy))
    · exact Filter.mem_of_superset (hE₁.mem_nhds hx) (fun y hy ↦ Or.inl (Or.inr hy))
    · exact hseam x hx
  · apply disjoint_left.mpr
    rintro x ⟨hx₁,hx₂⟩ ((hx | hx) | hx)
    · exact disjoint_left.mp hd₂ hx hx₂
    · exact disjoint_left.mp hd₁ hx₁ hx
    · exact disjoint_left.mp hCd₁ hx₁ ((hi.symm ▸ hdD hx).1)
  · ext x
    have hc₁x := Set.ext_iff.mp hc₁ x
    have hc₂x := Set.ext_iff.mp hc₂ x
    have hxsub : x ∈ C₂ → x ∈ C₁ := fun h ↦ hsub h
    have hxd : x ∈ d → x ∈ c₁ ∧ x ∈ c₂ := fun h ↦ show x ∈ c₁ ∩ c₂ from hi.symm ▸ hdD h
    have hxc₂ : x ∈ c₂ → x ∈ C₁ ∨ x ∈ c₁ := fun h ↦ hc₂cl h
    have hd1x : ¬(x ∈ C₁ ∧ x ∈ E₁) := fun h ↦ disjoint_left.mp hd₁ h.1 h.2
    have hd2x : ¬(x ∈ C₂ ∧ x ∈ E₂) := fun h ↦ disjoint_left.mp hd₂ h.1 h.2
    simp only [mem_union, mem_inter_iff, mem_compl_iff, mem_sdiff] at hc₁x hc₂x ⊢
    clear hC₁ hE₁ hC₂ hE₂ hd₁ hd₂ hc₁ hc₂ hcl₁ hcl₂ hecl₁ hecl₂ hi hdD
      harc₁ harc₂ hsub hseam hCd₁ hEd₁ hCd₂ hEd₂ hc₂cl ha₁ ha₂ hacc
      hfront₁ hfront₂ hfront
    tauto
  · rintro x ⟨hx,hxd⟩
    rcases hx with hx | hx
    · exact closure_mono (fun y hy ↦ Or.inl (Or.inr hy)) (hecl₁ hx)
    · exact closure_mono (fun y hy ↦ Or.inl (Or.inl hy)) (hcl₂ hx)

end HolomorphicAnosov
