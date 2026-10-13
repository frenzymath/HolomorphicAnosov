import HolomorphicAnosov.Topology.ClosedContactGapOrderG2

open Set
namespace HolomorphicAnosov

/-- Two simple arcs have the same order on their common retained contacts if
contact-free gaps of the first have contact-free endpoint intervals on the second.
Source: Cairns (1951), §3(E), p.863; agent-written reduction to closed-contact
interval gap filling. Pull the closed contacts back to the first interval and
compose their points with the inverse second parametrization. This partial map
is continuous and injective and fixes both endpoints. The gap hypothesis says
that its unordered target intervals avoid its contact image. The closed-contact
gap-order theorem makes it strictly increasing, proving order agreement. -/
theorem arc_contact_order_g2 (α m : unitInterval → ℂ)
    (hα : _root_.Topology.IsEmbedding α) (hm : _root_.Topology.IsEmbedding m)
    (C : Set ℂ) (hC : IsClosed C) (hCm : C ⊆ range m)
    (h0 : α 0=m 0) (h1 : α 1=m 1) (hC0 : α 0 ∈ C) (hC1 : α 1 ∈ C)
    (hgap : ∀ l r : unitInterval, l<r → α l ∈ C → α r ∈ C →
      Disjoint (α '' Ioo l r) C → ∀ p q : unitInterval, m p=α l → m q=α r →
      Disjoint (m '' Ioo (min p q) (max p q)) C) :
    ∀ s t p q : unitInterval, α s ∈ C → α t ∈ C →
      α s=m p → α t=m q → (s ≤ t ↔ p ≤ q) := by
  classical
  let F : Set unitInterval := α ⁻¹' C
  let f : unitInterval → unitInterval := fun t ↦ Function.invFun m (α t)
  have heval : ∀ t ∈ F, m (f t)=α t := fun t ht ↦ Function.invFun_eq (hCm ht)
  have hcont : ContinuousOn f F := by
    apply hm.continuousOn_iff.mpr
    exact hα.continuous.continuousOn.congr heval
  have hinj : InjOn f F := by
    intro s hs t ht he
    apply hα.injective
    rw [← heval s hs,← heval t ht,he]
  have hf0 : f 0=0 := hm.injective ((heval 0 hC0).trans h0)
  have hf1 : f 1=1 := hm.injective ((heval 1 hC1).trans h1)
  have havoid : ∀ l r : unitInterval, l ∈ F → r ∈ F → l<r → Disjoint (Ioo l r) F →
      Disjoint (Ioo (min (f l) (f r)) (max (f l) (f r))) (f '' F) := by
    intro l r hl hr hlr hd
    have hαgap : Disjoint (α '' Ioo l r) C := by
      apply disjoint_left.mpr
      rintro z ⟨t,ht,rfl⟩ hc
      exact disjoint_left.mp hd ht hc
    have hmgap := hgap l r hlr hl hr hαgap (f l) (f r) (heval l hl) (heval r hr)
    apply disjoint_left.mpr
    rintro x hx ⟨t,ht,rfl⟩
    exact disjoint_left.mp hmgap (mem_image_of_mem m hx) ((heval t ht).symm ▸ ht)
  have hmono := closed_contact_unitInterval_order_g2 F f (hC.preimage hα.continuous)
    hC0 hC1 hcont hinj hf0 hf1 havoid
  intro s t p q hs ht hsp htq
  have hfs : f s=p := hm.injective ((heval s hs).trans hsp)
  have hft : f t=q := hm.injective ((heval t ht).trans htq)
  constructor
  · intro hst
    rcases eq_or_lt_of_le hst with he | he
    · subst t
      exact (hfs.symm.trans hft).le
    · simpa only [hfs,hft] using (hmono hs ht he).le
  · intro hpq
    by_contra hn
    have hh := hmono ht hs (lt_of_not_ge hn)
    rw [hfs,hft] at hh
    exact hh.not_ge hpq

end HolomorphicAnosov
