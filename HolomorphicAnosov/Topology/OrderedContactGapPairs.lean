import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic

universe u v
open Set
namespace HolomorphicAnosov

/-- A contact-order equivalence preserves the ordered endpoints of contact-free gaps. (Cairns, §3(D,E)) -/
theorem ordered_contact_gap_pairs {I J : Type u} {X : Type v} [LinearOrder I] [LinearOrder J]
    (f : I → X) (g : J → X) (C : Set X)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hCf : C ⊆ range f) (hCg : C ⊆ range g)
    (horder : ∀ u v s t, f u ∈ C → f v ∈ C →
      g s = f u → g t = f v → (u ≤ v ↔ s ≤ t)) :
    {p : X × X | ∃ l r, l < r ∧ f l ∈ C ∧ f r ∈ C ∧
      (∀ t, l < t → t < r → f t ∉ C) ∧ p = (f l, f r)} =
    {p : X × X | ∃ l r, l < r ∧ g l ∈ C ∧ g r ∈ C ∧
      (∀ t, l < t → t < r → g t ∉ C) ∧ p = (g l, g r)} := by
  have transfer {A B : Type u} [LinearOrder A] [LinearOrder B]
      (a : A → X) (b : B → X) (ha : Function.Injective a)
      (hCa : C ⊆ range a) (hCb : C ⊆ range b)
      (ho : ∀ u v s t, a u ∈ C → a v ∈ C →
        b s = a u → b t = a v → (u ≤ v ↔ s ≤ t)) :
      {p : X × X | ∃ l r, l < r ∧ a l ∈ C ∧ a r ∈ C ∧
        (∀ t, l < t → t < r → a t ∉ C) ∧ p = (a l, a r)} ⊆
      {p : X × X | ∃ l r, l < r ∧ b l ∈ C ∧ b r ∈ C ∧
        (∀ t, l < t → t < r → b t ∉ C) ∧ p = (b l, b r)} := by
    rintro p ⟨l,r,hlr,hl,hr,hgap,rfl⟩
    obtain ⟨s, hs⟩ := hCb hl
    obtain ⟨t, ht⟩ := hCb hr
    have hst : s < t := by
      apply lt_of_le_of_ne ((ho l r s t hl hr hs ht).mp hlr.le)
      intro he
      exact hlr.ne (ha (hs.symm.trans ((congrArg b he).trans ht)))
    refine ⟨s,t,hst,hs.symm ▸ hl,ht.symm ▸ hr,?_,by rw [hs,ht]⟩
    intro w hsw hwt hw
    obtain ⟨u, hu⟩ := hCa hw
    have hlu : l < u := by
      apply lt_of_not_ge
      intro hul
      have hus := (ho u l w s (hu ▸ hw) hl hu.symm hs).mp hul
      exact (not_le_of_gt hsw) hus
    have hur : u < r := by
      apply lt_of_not_ge
      intro hru
      have htw := (ho r u t w hr (hu ▸ hw) ht hu.symm).mp hru
      exact (not_le_of_gt hwt) htw
    exact hgap u hlu hur (hu ▸ hw)
  apply subset_antisymm (transfer f g hf hCf hCg horder)
  apply transfer g f hg hCg hCf
  intro u v s t hu hv hs ht
  exact (horder s t u v (hs.symm ▸ hu) (ht.symm ▸ hv) hs.symm ht.symm).symm

end HolomorphicAnosov
