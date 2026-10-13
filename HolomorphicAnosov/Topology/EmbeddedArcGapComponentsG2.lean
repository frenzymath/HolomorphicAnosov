import HolomorphicAnosov.Topology.ClosedContactGapOrderG2

open Set
namespace HolomorphicAnosov

lemma interval_contact_gap_component_g2 (F : Set unitInterval) {l r x : unitInterval}
    (hl : l ∈ F) (hr : r ∈ F) (hgap : Disjoint (Ioo l r) F) (hx : x ∈ Ioo l r) :
    connectedComponentIn Fᶜ x=Ioo l r := by
  have hsub : Ioo l r ⊆ Fᶜ := fun t ht hF ↦ disjoint_left.mp hgap ht hF
  apply Subset.antisymm
  · intro y hy
    have hc := isPreconnected_connectedComponentIn.ordConnected (s:=connectedComponentIn Fᶜ x)
    have hxc : x ∈ connectedComponentIn Fᶜ x := mem_connectedComponentIn (hsub hx)
    constructor
    · by_contra hn
      have hlc := hc.out hy hxc ⟨le_of_not_gt hn,hx.1.le⟩
      exact connectedComponentIn_subset Fᶜ x hlc hl
    · by_contra hn
      have hrc := hc.out hxc hy ⟨hx.2.le,le_of_not_gt hn⟩
      exact connectedComponentIn_subset Fᶜ x hrc hr
  · exact isPreconnected_Ioo.subset_connectedComponentIn hx hsub

/-- A contact-free open subarc with contact endpoints is exactly a connected
component after removing the contacts from an embedded arc. Source: Cairns
(1951), §3(D,E), p.863; elementary interval-component transport. The interval
component cannot cross either removed endpoint, since preconnected subsets of
a linear order contain every intervening point. Conversely the open interval
is preconnected and avoids all contacts. Transport through the embedded arc and
its continuous inverse identifies the corresponding component in the plane. -/
theorem embedded_arc_gap_component_g2 (α : unitInterval → ℂ)
    (hα : _root_.Topology.IsEmbedding α) (C : Set ℂ) {l r x : unitInterval}
    (hl : α l ∈ C) (hr : α r ∈ C) (hgap : Disjoint (α '' Ioo l r) C)
    (hx : x ∈ Ioo l r) :
    connectedComponentIn (range α \ C) (α x)=α '' Ioo l r := by
  classical
  let F : Set unitInterval := α ⁻¹' C
  let ψ : ℂ → unitInterval := Function.invFun α
  have hψα (t : unitInterval) : ψ (α t)=t := Function.leftInverse_invFun hα.injective t
  have hαψ : ∀ z ∈ range α, α (ψ z)=z := fun z hz ↦ Function.invFun_eq hz
  have hψcont : ContinuousOn ψ (range α) := by
    apply hα.continuousOn_iff.mpr
    exact continuous_id.continuousOn.congr hαψ
  have hgap' : Disjoint (Ioo l r) F := by
    apply disjoint_left.mpr
    intro t ht htc
    exact disjoint_left.mp hgap (mem_image_of_mem α ht) htc
  have hsubset : α '' Ioo l r ⊆ range α \ C := by
    rintro z ⟨t,ht,rfl⟩
    exact ⟨mem_range_self t,fun hc ↦ disjoint_left.mp hgap (mem_image_of_mem α ht) hc⟩
  have hxT := hsubset (mem_image_of_mem α hx)
  have hψT : ψ '' (range α \ C) ⊆ Fᶜ := by
    rintro t ⟨z,hz,rfl⟩ hc
    exact hz.2 ((hαψ z hz.1) ▸ hc)
  apply Subset.antisymm
  · intro z hz
    have hm := (hψcont.mono sdiff_subset).image_connectedComponentIn_subset hxT
      (mem_image_of_mem ψ hz)
    rw [hψα] at hm
    have hmc := connectedComponentIn_mono x hψT hm
    rw [interval_contact_gap_component_g2 F hl hr hgap' hx] at hmc
    exact ⟨ψ z,hmc,hαψ z (connectedComponentIn_subset _ _ hz).1⟩
  · exact (isPreconnected_Ioo.image α hα.continuous.continuousOn).subset_connectedComponentIn
      (mem_image_of_mem α hx) hsubset

lemma contact_parameter_gaps_countable_g2 {X : Type*} (f : unitInterval → X) (C : Set X) :
    let G : Set (unitInterval × unitInterval) :=
      {g | g.1<g.2 ∧ f g.1 ∈ C ∧ f g.2 ∈ C ∧ Disjoint (f '' Ioo g.1 g.2) C}
    G.Countable ∧ G.Pairwise (fun g h ↦ Disjoint (Ioo g.1 g.2) (Ioo h.1 h.2)) := by
  intro G
  have hpair : G.Pairwise (fun g h ↦ Disjoint (Ioo g.1 g.2) (Ioo h.1 h.2)) := by
    intro g hg h hh hne
    apply disjoint_left.mpr
    intro x hx hx'
    have hdis (k : unitInterval × unitInterval) (hk : k ∈ G) :
        Disjoint (Ioo k.1 k.2) (f ⁻¹' C) := by
      apply disjoint_left.mpr
      intro t ht htc
      exact disjoint_left.mp hk.2.2.2 (mem_image_of_mem f ht) htc
    obtain ⟨hl,hr⟩ := contact_gap_endpoints_unique_g2 (f ⁻¹' C)
      hg.2.1 hg.2.2.1 hh.2.1 hh.2.2.1 (hdis g hg) (hdis h hh) hx hx'
    exact hne (Prod.ext hl hr)
  refine ⟨?_,hpair⟩
  exact Set.PairwiseDisjoint.countable_of_isOpen
    (s:=fun g : unitInterval × unitInterval ↦ Ioo g.1 g.2) hpair
    (fun g hg ↦ isOpen_Ioo) (fun g hg ↦ nonempty_Ioo.mpr hg.1)

lemma exists_unitInterval_contact_gap_g2 (F : Set unitInterval) (hF : IsClosed F)
    (h0 : (0:unitInterval) ∈ F) (h1 : (1:unitInterval) ∈ F)
    {t : unitInterval} (ht : t ∉ F) :
    ∃ l r : unitInterval, l ∈ F ∧ r ∈ F ∧ l<t ∧ t<r ∧ Disjoint (Ioo l r) F := by
  let R : Set ℝ := Subtype.val '' F
  have hR : IsClosed R := (hF.isCompact.image continuous_subtype_val).isClosed
  have hRsub : R ⊆ Icc (0:ℝ) 1 := by rintro x ⟨s,hs,rfl⟩; exact s.property
  have htR : (t:ℝ) ∉ R := by
    rintro ⟨s,hs,he⟩
    exact ht ((Subtype.ext he : s=t) ▸ hs)
  obtain ⟨l,r,⟨u,hu,rfl⟩,⟨v,hv,rfl⟩,hlt,htr,hd⟩ :=
    exists_closed_contact_gap R hR hRsub ⟨0,h0,rfl⟩ ⟨1,h1,rfl⟩ t.property htR
  refine ⟨u,v,hu,hv,hlt,htr,?_⟩
  apply disjoint_left.mpr
  intro x hx hxF
  exact disjoint_left.mp hd hx (mem_image_of_mem Subtype.val hxF)

end HolomorphicAnosov
