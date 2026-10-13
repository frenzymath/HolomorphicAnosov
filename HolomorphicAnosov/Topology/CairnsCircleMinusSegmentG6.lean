import HolomorphicAnosov.Topology.CairnsHalfDiskBoundaryTransport
import Mathlib.Analysis.Convex.PathConnected

open Set
namespace HolomorphicAnosov

/-- Removing an embedded straight closed segment from a topological circle leaves a
preconnected set. Cairns (1951), preliminary 2(B) and Theorem 2.1: the remaining open
boundary arc. Transport the segment into the unit circle; the existing embedded-arc
classification identifies it with one directed closed circle arc, whose complement
is the reverse open arc. Transport that connected open arc back. -/
theorem cairns_circle_minus_segment_data_g6
    (c : Set ℂ) (e : c ≃ₜ Metric.sphere (0 : ℂ) 1)
    (a b : ℂ) (hab : a ≠ b) (hsub : segment ℝ a b ⊆ c) :
    IsPreconnected (c \ segment ℝ a b) ∧
      closure (c \ segment ℝ a b) = c \ openSegment ℝ a b := by
  let p : Path a b := Path.segment a b
  have hp : Function.Injective p := Path.segment_injective_of_ne hab
  have hprange : range p = segment ℝ a b := Path.range_segment a b
  let f : unitInterval → Circle := fun t ↦ e ⟨p t, hsub (hprange ▸ mem_range_self t)⟩
  have hfcont : Continuous f := e.continuous.comp (p.continuous.subtype_mk _)
  have hfinj : Function.Injective f := by
    intro s t h
    apply hp
    exact congrArg Subtype.val (e.injective h)
  have hf : _root_.Topology.IsEmbedding f := hfcont.isClosedEmbedding hfinj |>.isEmbedding
  have hab' : f 0 ≠ f 1 := hfinj.ne zero_ne_one
  have hpre : IsPreconnected (range f)ᶜ := by
    rcases Topology.cairns_circle_arc_range f hf with h | h
    · rw [h, Circle.compl_range_path hab']
      exact isPreconnected_Ioo.image _ (Circle.path (f 1) (f 0)).continuous.continuousOn
    · rw [h, Circle.compl_range_path hab'.symm]
      exact isPreconnected_Ioo.image _ (Circle.path (f 0) (f 1)).continuous.continuousOn
  let g : Circle → ℂ := fun z ↦ (e.symm z : ℂ)
  have hgcont : Continuous g := e.symm.continuous.subtype_val
  have hginj : Function.Injective g := Subtype.val_injective.comp e.symm.injective
  have hgrange : range g = c := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact (e.symm w).property
    · intro hz
      exact ⟨e ⟨z, hz⟩, by simp [g]⟩
  have hgf : g '' range f = segment ℝ a b := by
    rw [← range_comp]
    have heq : g ∘ f = p := by
      funext t
      change (e.symm (e ⟨p t, _⟩) : ℂ) = p t
      exact congrArg Subtype.val (e.symm_apply_apply _)
    rw [heq, hprange]
  have him : g '' (range f)ᶜ = c \ segment ℝ a b := by
    rw [compl_eq_univ_sdiff, image_sdiff hginj, image_univ, hgrange, hgf]
  refine ⟨him ▸ hpre.image g hgcont.continuousOn, ?_⟩
  have hclass : closure (range f)ᶜ = (range f \ {f 0, f 1})ᶜ := by
    rcases Topology.cairns_circle_arc_range f hf with h | h
    · rw [h, Circle.compl_range_path hab',
        Topology.cairns_directed_circle_arc_closure _ _ hab'.symm]
      have hu := Circle.range_path_union_range_path hab'
      have hi := Circle.range_path_inter_range_path hab'
      ext z
      have hzu : z ∈ range (Circle.path (f 0) (f 1)) ∪
          range (Circle.path (f 1) (f 0)) := hu.symm ▸ mem_univ z
      have hzi : z ∈ range (Circle.path (f 0) (f 1)) ∩
          range (Circle.path (f 1) (f 0)) ↔ z ∈ ({f 0, f 1} : Set Circle) :=
        Set.ext_iff.mp hi z
      simp only [mem_union, mem_inter_iff, mem_insert_iff, mem_singleton_iff] at hzu hzi
      simp only [mem_compl_iff, mem_sdiff, mem_insert_iff, mem_singleton_iff]
      tauto
    · rw [h, Circle.compl_range_path hab'.symm,
        Topology.cairns_directed_circle_arc_closure _ _ hab']
      have hu := Circle.range_path_union_range_path hab'
      have hi := Circle.range_path_inter_range_path hab'
      ext z
      have hzu : z ∈ range (Circle.path (f 0) (f 1)) ∪
          range (Circle.path (f 1) (f 0)) := hu.symm ▸ mem_univ z
      have hzi : z ∈ range (Circle.path (f 0) (f 1)) ∩
          range (Circle.path (f 1) (f 0)) ↔ z ∈ ({f 0, f 1} : Set Circle) :=
        Set.ext_iff.mp hi z
      simp only [mem_union, mem_inter_iff, mem_insert_iff, mem_singleton_iff] at hzu hzi
      simp only [mem_compl_iff, mem_sdiff, mem_insert_iff, mem_singleton_iff]
      tauto
  have hgf0 : g (f 0) = a := by
    change (e.symm (e ⟨p 0, _⟩) : ℂ) = a
    simp only [Homeomorph.symm_apply_apply]
    exact p.source
  have hgf1 : g (f 1) = b := by
    change (e.symm (e ⟨p 1, _⟩) : ℂ) = b
    simp only [Homeomorph.symm_apply_apply]
    exact p.target
  have hopen : g '' (range f \ {f 0, f 1}) = openSegment ℝ a b := by
    rw [image_sdiff hginj, hgf, image_pair, hgf0, hgf1]
    ext z
    rw [← insert_endpoints_openSegment]
    have hne0 : a ∉ openSegment ℝ a b := fun h ↦ hab (left_mem_openSegment_iff.mp h)
    have hne1 : b ∉ openSegment ℝ a b := fun h ↦ hab (right_mem_openSegment_iff.mp h)
    simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
    constructor
    · tauto
    · intro hz
      exact ⟨Or.inr (Or.inr hz), fun h ↦ h.elim (fun h ↦ hne0 (h ▸ hz))
        (fun h ↦ hne1 (h ▸ hz))⟩
  rw [← him, (hgcont.isClosedEmbedding hginj).closure_image_eq, hclass,
    compl_eq_univ_sdiff, image_sdiff hginj, image_univ, hgrange, hopen]

/-- The complementary open arc is preconnected. -/
theorem cairns_circle_minus_segment_preconnected_g6
    (c : Set ℂ) (e : c ≃ₜ Metric.sphere (0 : ℂ) 1)
    (a b : ℂ) (hab : a ≠ b) (hsub : segment ℝ a b ⊆ c) :
    IsPreconnected (c \ segment ℝ a b) :=
  (cairns_circle_minus_segment_data_g6 c e a b hab hsub).1

end HolomorphicAnosov
