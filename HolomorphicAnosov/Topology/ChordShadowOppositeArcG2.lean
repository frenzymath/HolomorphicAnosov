import Mathlib.Topology.Subpath
import HolomorphicAnosov.Topology.Plane.CairnsChordSectorSeparation

open Set
namespace HolomorphicAnosov

lemma path_subpath_injective_g2 {X : Type*} [TopologicalSpace X] {A B : X}
    (μ : Path A B) (hμ : Function.Injective μ) {p q : unitInterval} (hpq : p ≠ q) :
    Function.Injective (μ.subpath p q) := by
  intro x y he
  have hh := congrArg Subtype.val (hμ he)
  change (1-(x:ℝ))*(p:ℝ)+(x:ℝ)*(q:ℝ)=
    (1-(y:ℝ))*(p:ℝ)+(y:ℝ)*(q:ℝ) at hh
  apply Subtype.ext
  have hzero : ((x:ℝ)-y)*((q:ℝ)-p)=0 := by nlinarith [hh]
  have hqp : (q:ℝ) ≠ (p:ℝ) := fun he ↦ hpq (Subtype.ext he.symm)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr hqp))

/-- A connected shadow on one side of an interior chord cannot approach the
opposite open curve arc. Source: Cairns (1951), Lemma 3.1 and §3(E), pp.861–863;
agent-written consequence of the labeled chord-sector theorem. The connected
shadow lies in one chord sector. A curve mark in its closure outside the chosen
closed arc excludes that arc's sector, by the sector frontier bound. Every point
of the chosen open arc is outside the other sector's frontier as well, since the
two closed arcs meet only at the chord endpoints. -/
theorem chord_shadow_opposite_arc_g2
    (c : Circle → ℂ) (hc : _root_.Topology.IsEmbedding c)
    (γ : unitInterval → Circle) (hγ : _root_.Topology.IsEmbedding γ)
    (a S : Set ℂ) (haBounded : Bornology.IsBounded a)
    (haComponent : ∃ z ∈ a, connectedComponentIn (range c)ᶜ z=a)
    (hChord : openSegment ℝ (c (γ 0)) (c (γ 1)) ⊆ a)
    (hS : IsConnected S) (hSa : S ⊆ a \ openSegment ℝ (c (γ 0)) (c (γ 1)))
    (mark : Circle) (hmark : mark ∉ range γ) (hmarkS : c mark ∈ closure S) :
    ∀ t ∈ Ioo (0:unitInterval) 1, c (γ t) ∉ closure S := by
  have hpq : γ 0 ≠ γ 1 := hγ.injective.ne zero_ne_one
  have hcompArc : ∃ δ : Path (γ 0) (γ 1), _root_.Topology.IsEmbedding δ ∧
      range γ ∪ range δ=univ ∧ range γ ∩ range δ={γ 0,γ 1} := by
    rcases Topology.cairns_circle_arc_range γ hγ with h | h
    · let δ := (Circle.path (γ 1) (γ 0)).symm
      have hi : Function.Injective δ := by
        intro x y he
        exact unitInterval.symm_inj.mp ((Circle.path_injective_of_ne hpq.symm) he)
      refine ⟨δ,(δ.continuous.isClosedEmbedding hi).isEmbedding,?_,?_⟩
      · rw [h,Path.symm_range]
        exact Circle.range_path_union_range_path hpq
      · rw [h,Path.symm_range]
        exact Circle.range_path_inter_range_path hpq
    · let δ := Circle.path (γ 0) (γ 1)
      refine ⟨δ,(δ.continuous.isClosedEmbedding (Circle.path_injective_of_ne hpq)).isEmbedding,?_,?_⟩
      · rw [h,union_comm]
        exact Circle.range_path_union_range_path hpq
      · rw [h,inter_comm]
        exact Circle.range_path_inter_range_path hpq
  obtain ⟨δ,hδ,hcover,hmeet⟩ := hcompArc
  have haSub : a ⊆ (range c)ᶜ := by
    obtain ⟨z,hz,he⟩ := haComponent
    rw [← he]
    exact connectedComponentIn_subset _ _
  have hane : a.Nonempty := hS.nonempty.mono (hSa.trans sdiff_subset)
  obtain ⟨V,W,hVne,hWne,hVconn,hWconn,hVo,hWo,hdis,hVW,hcomponents,hVfront,hWfront,hlocal⟩ :=
    cairns_chord_sector_separation c hc (γ 0) (γ 1) hpq γ δ hγ hδ rfl rfl δ.source δ.target
      hcover hmeet a hane haBounded haComponent hChord
  have hVa : V ⊆ a := by
    intro z hz
    exact (hVW.symm ▸ (show z ∈ V ∪ W from Or.inl hz)).1
  have hWa : W ⊆ a := by
    intro z hz
    exact (hVW.symm ▸ (show z ∈ V ∪ W from Or.inr hz)).1
  have hcurveSeg : ∀ z : Circle, c z ∈ segment ℝ (c (γ 0)) (c (γ 1)) →
      z=γ 0 ∨ z=γ 1 := by
    intro z hz
    rw [← insert_endpoints_openSegment] at hz
    rcases hz with he | he | hi
    · exact Or.inl (hc.injective he)
    · exact Or.inr (hc.injective he)
    · exact False.elim (haSub (hChord hi) ⟨z,rfl⟩)
  have hcurveFront {T : Set ℂ} (hTa : T ⊆ a) {z : Circle} (hz : c z ∈ closure T) :
      c z ∈ frontier T := by
    exact ⟨hz,fun hi ↦ haSub (hTa (interior_subset hi)) ⟨z,rfl⟩⟩
  obtain ⟨z,hz⟩ := hS.nonempty
  have hSc := hS.isPreconnected.subset_connectedComponentIn hz hSa
  have hSW : S ⊆ W := by
    rcases hcomponents z (hSa hz) with he | he
    · have hSV : S ⊆ V := he ▸ hSc
      have hf := hVfront (hcurveFront hVa (closure_mono hSV hmarkS))
      rcases hf with hs | hi
      · rcases hcurveSeg mark hs with he | he
        · exact False.elim (hmark ⟨0,he.symm⟩)
        · exact False.elim (hmark ⟨1,he.symm⟩)
      · obtain ⟨p,hp,he⟩ := hi
        exact False.elim (hmark (hc.injective he ▸ hp))
    · exact he ▸ hSc
  intro t ht hct
  have hf := hWfront (hcurveFront hWa (closure_mono hSW hct))
  have hnotends : γ t ≠ γ 0 ∧ γ t ≠ γ 1 :=
    ⟨hγ.injective.ne ht.1.ne',hγ.injective.ne ht.2.ne⟩
  rcases hf with hs | hi
  · exact (hcurveSeg (γ t) hs).elim hnotends.1 hnotends.2
  · obtain ⟨p,hp,he⟩ := hi
    have hboth : γ t ∈ range γ ∩ range δ := ⟨⟨t,rfl⟩,hc.injective he ▸ hp⟩
    rw [hmeet] at hboth
    exact hboth.elim hnotends.1 (fun he ↦ hnotends.2 (mem_singleton_iff.mp he))

lemma chord_shadow_opposite_subpath_g2
    (c : Circle → ℂ) (hc : _root_.Topology.IsEmbedding c)
    {A B : ℂ} (μ : Path A B) (hμ : Function.Injective μ) (hμc : range μ ⊆ range c)
    (p q : unitInterval) (hpq : p<q) (a S : Set ℂ) (haBounded : Bornology.IsBounded a)
    (haComponent : ∃ z ∈ a, connectedComponentIn (range c)ᶜ z=a)
    (hChord : openSegment ℝ (μ p) (μ q) ⊆ a)
    (hS : IsConnected S) (hSa : S ⊆ a \ openSegment ℝ (μ p) (μ q))
    (mark : Circle) (hmark : c mark ∉ range μ) (hmarkS : c mark ∈ closure S) :
    ∀ r ∈ Ioo p q, μ r ∉ closure S := by
  let ν := μ.subpath p q
  have hν : Function.Injective ν := path_subpath_injective_g2 μ hμ hpq.ne
  let γ : unitInterval → Circle := fun t ↦ hc.toHomeomorph.symm
    ⟨ν t,hμc ⟨Icc.convexComb p q t,rfl⟩⟩
  have hγcont : Continuous γ := hc.toHomeomorph.symm.continuous.comp (ν.continuous.subtype_mk _)
  have heval (t : unitInterval) : c (γ t)=ν t :=
    congrArg Subtype.val (hc.toHomeomorph.apply_symm_apply _)
  have hγ : _root_.Topology.IsEmbedding γ := by
    apply (hγcont.isClosedEmbedding ?_).isEmbedding
    intro x y he
    apply hν
    simpa only [heval] using congrArg c he
  have he0 : c (γ 0)=μ p := (heval 0).trans ν.source
  have he1 : c (γ 1)=μ q := (heval 1).trans ν.target
  have hmarkγ : mark ∉ range γ := by
    rintro ⟨t,ht⟩
    apply hmark
    rw [← ht,heval]
    exact ⟨Icc.convexComb p q t,rfl⟩
  have havoid := chord_shadow_opposite_arc_g2 c hc γ hγ a S haBounded haComponent
    (by simpa only [he0,he1] using hChord) hS
    (by simpa only [he0,he1] using hSa) mark hmarkγ hmarkS
  intro r hr hrc
  have hrange : r ∈ range (Icc.convexComb p q) := by
    rw [Path.range_subpathAux,uIcc_of_le hpq.le]
    exact ⟨hr.1.le,hr.2.le⟩
  obtain ⟨t,ht⟩ := hrange
  have ht0 : t ≠ 0 := by
    intro he
    subst t
    have hp : p=r := by simpa using ht
    exact hr.1.ne hp
  have ht1 : t ≠ 1 := by
    intro he
    subst t
    have hq : q=r := by simpa using ht
    exact hr.2.ne' hq
  apply havoid t ⟨lt_of_le_of_ne bot_le ht0.symm,lt_of_le_of_ne le_top ht1⟩
  rw [heval]
  change μ (Icc.convexComb p q t) ∈ closure S
  exact ht.symm ▸ hrc

end HolomorphicAnosov
