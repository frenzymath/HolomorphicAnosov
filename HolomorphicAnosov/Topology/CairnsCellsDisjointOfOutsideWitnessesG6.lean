import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded

open Set
namespace HolomorphicAnosov

/-- For two bounded Jordan cells with a common boundary arc, opposite exterior witnesses
force their closed cells to meet only in that arc. Cairns (1951), Theorem 2.1, the
non-nesting argument in the diagonal induction: each complementary boundary arc lies
wholly in one region of the other circle; boundedness excludes its being the inside. -/
theorem cairns_cells_disjoint_of_outside_witnesses_g6
    {X : Type*} [TopologicalSpace X] [Bornology X]
    {C₁ E₁ c₁ C₂ E₂ c₂ D : Set X}
    (hC₁ : IsPreconnected C₁) (hE₁ : IsPreconnected E₁)
    (hC₂ : IsPreconnected C₂) (hE₂ : IsPreconnected E₂)
    (hoC₁ : IsOpen C₁) (hoE₁ : IsOpen E₁)
    (hoC₂ : IsOpen C₂) (hoE₂ : IsOpen E₂)
    (hd₁ : Disjoint C₁ E₁) (hd₂ : Disjoint C₂ E₂)
    (hc₁ : C₁ ∪ E₁ = c₁ᶜ) (hc₂ : C₂ ∪ E₂ = c₂ᶜ)
    (hcl₁ : closure C₁ = C₁ ∪ c₁) (hcl₂ : closure C₂ = C₂ ∪ c₂)
    (hb₁ : Bornology.IsBounded C₁) (hb₂ : Bornology.IsBounded C₂)
    (hu₁ : ¬Bornology.IsBounded E₁) (hu₂ : ¬Bornology.IsBounded E₂)
    (hi : c₁ ∩ c₂ = D)
    (ha₁ : IsPreconnected (c₁ \ D)) (ha₂ : IsPreconnected (c₂ \ D))
    (hw₁ : (C₁ ∩ E₂).Nonempty) (hw₂ : (C₂ ∩ E₁).Nonempty) :
    closure C₁ ∩ closure C₂ = D := by
  have hdis₁ : Disjoint E₁ (closure C₁) := by
    rw [hcl₁]
    apply disjoint_union_right.mpr
    refine ⟨hd₁.symm, disjoint_left.mpr ?_⟩
    intro x hx hc
    exact (show x ∈ c₁ᶜ from hc₁ ▸ Or.inr hx) hc
  have hdis₂ : Disjoint E₂ (closure C₂) := by
    rw [hcl₂]
    apply disjoint_union_right.mpr
    refine ⟨hd₂.symm, disjoint_left.mpr ?_⟩
    intro x hx hc
    exact (show x ∈ c₂ᶜ from hc₂ ▸ Or.inr hx) hc
  have hE₁E₂ (h : c₂ ⊆ closure C₁) : E₁ ⊆ E₂ := by
    have hsub : E₁ ⊆ C₂ ∪ E₂ := by
      rw [hc₂]
      intro x hx hxc
      exact disjoint_left.mp hdis₁ hx (h hxc)
    rcases hE₁.subset_or_subset hoC₂ hoE₂ hd₂ hsub with hsub | hsub
    · exact (hu₁ (hb₂.subset hsub)).elim
    · exact hsub
  have hE₂E₁ (h : c₁ ⊆ closure C₂) : E₂ ⊆ E₁ := by
    have hsub : E₂ ⊆ C₁ ∪ E₁ := by
      rw [hc₁]
      intro x hx hxc
      exact disjoint_left.mp hdis₂ hx (h hxc)
    rcases hE₂.subset_or_subset hoC₁ hoE₁ hd₁ hsub with hsub | hsub
    · exact (hu₂ (hb₁.subset hsub)).elim
    · exact hsub
  have hArc₂ : c₂ \ D ⊆ E₁ := by
    have hsub : c₂ \ D ⊆ C₁ ∪ E₁ := by
      rw [hc₁]
      rintro x ⟨hx₂, hxD⟩ hx₁
      exact hxD (hi ▸ ⟨hx₁, hx₂⟩)
    rcases ha₂.subset_or_subset hoC₁ hoE₁ hd₁ hsub with hsub | hsub
    · have hcontain : c₂ ⊆ closure C₁ := by
        intro x hx
        rw [hcl₁]
        by_cases hxD : x ∈ D
        · exact Or.inr ((hi.symm ▸ hxD : x ∈ c₁ ∩ c₂).1)
        · exact Or.inl (hsub ⟨hx, hxD⟩)
      obtain ⟨x, hx₂, hx₁⟩ := hw₂
      exact (disjoint_left.mp hd₂ hx₂ (hE₁E₂ hcontain hx₁)).elim
    · exact hsub
  have hArc₁ : c₁ \ D ⊆ E₂ := by
    have hsub : c₁ \ D ⊆ C₂ ∪ E₂ := by
      rw [hc₂]
      rintro x ⟨hx₁, hxD⟩ hx₂
      exact hxD (hi ▸ ⟨hx₁, hx₂⟩)
    rcases ha₁.subset_or_subset hoC₂ hoE₂ hd₂ hsub with hsub | hsub
    · have hcontain : c₁ ⊆ closure C₂ := by
        intro x hx
        rw [hcl₂]
        by_cases hxD : x ∈ D
        · exact Or.inr ((hi.symm ▸ hxD : x ∈ c₁ ∩ c₂).2)
        · exact Or.inl (hsub ⟨hx, hxD⟩)
      obtain ⟨x, hx₁, hx₂⟩ := hw₁
      exact (disjoint_left.mp hd₁ hx₁ (hE₂E₁ hcontain hx₂)).elim
    · exact hsub
  have hC₁E₂ : C₁ ⊆ E₂ := by
    have hsub : C₁ ⊆ C₂ ∪ E₂ := by
      rw [hc₂]
      intro x hx hx₂
      by_cases hxD : x ∈ D
      · exact (show x ∈ c₁ᶜ from hc₁ ▸ Or.inl hx) (hi.symm ▸ hxD).1
      · exact disjoint_left.mp hd₁ hx (hArc₂ ⟨hx₂, hxD⟩)
    rcases hC₁.subset_or_subset hoC₂ hoE₂ hd₂ hsub with hsub | hsub
    · obtain ⟨x, hx₁, hx₂⟩ := hw₁
      exact (disjoint_left.mp hd₂ (hsub hx₁) hx₂).elim
    · exact hsub
  have hC₂E₁ : C₂ ⊆ E₁ := by
    have hsub : C₂ ⊆ C₁ ∪ E₁ := by
      rw [hc₁]
      intro x hx hx₁
      by_cases hxD : x ∈ D
      · exact (show x ∈ c₂ᶜ from hc₂ ▸ Or.inl hx) (hi.symm ▸ hxD).2
      · exact disjoint_left.mp hd₂ hx (hArc₁ ⟨hx₁, hxD⟩)
    rcases hC₂.subset_or_subset hoC₁ hoE₁ hd₁ hsub with hsub | hsub
    · obtain ⟨x, hx₂, hx₁⟩ := hw₂
      exact (disjoint_left.mp hd₁ (hsub hx₂) hx₁).elim
    · exact hsub
  apply subset_antisymm
  · rintro x ⟨hx₁, hx₂⟩
    have hxc₁ : x ∈ c₁ := by
      rcases hcl₁ ▸ hx₁ with h | h
      · exact (disjoint_left.mp hdis₂ (hC₁E₂ h) hx₂).elim
      · exact h
    have hxc₂ : x ∈ c₂ := by
      rcases hcl₂ ▸ hx₂ with h | h
      · exact (disjoint_left.mp hdis₁ (hC₂E₁ h) hx₁).elim
      · exact h
    exact hi ▸ ⟨hxc₁, hxc₂⟩
  · intro x hx
    have hh : x ∈ c₁ ∩ c₂ := hi.symm ▸ hx
    exact ⟨hcl₁.symm ▸ Or.inr hh.1, hcl₂.symm ▸ Or.inr hh.2⟩

end HolomorphicAnosov
