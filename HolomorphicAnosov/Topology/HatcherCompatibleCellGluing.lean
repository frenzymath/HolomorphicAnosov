import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.ContinuousMap.Basic

namespace HolomorphicAnosov

open Set

/-- Compatible maps on locally finite closed pieces of a complement glue to
a total map fixing the carrier, continuous on the ambient image of the pieces.

Source: Hatcher, Algebraic Topology, Theorem A.7, p.526, gluing the selected
cell extensions. At a point in the union choose a piece containing it; overlap
compatibility makes this choice irrelevant. On each piece the resulting map
equals the prescribed continuous map, and locally finite closed pasting gives
continuity on the union in the complement. The subtype inclusion induces the
ambient topology, so this is continuity on its ambient image. Define the total
map to be the identity on the carrier and use any fixed carrier point off the
carrier and selected pieces. No continuity at the carrier is asserted here;
that follows later from quantitative image control. The index type may be empty. -/
theorem hatcher_compatible_cell_gluing
    {E : Type*} [TopologicalSpace E] {ι : Type*}
    (C : Set E) (hne : C.Nonempty)
    (A : ι → Set {x : E // x ∉ C})
    (hfinite : LocallyFinite A) (hclosed : ∀ i, IsClosed (A i))
    (f : ∀ i, C(A i, C))
    (hcompat : ∀ i j x (hi : x ∈ A i) (hj : x ∈ A j),
      f i ⟨x, hi⟩ = f j ⟨x, hj⟩) :
    ∃ r : E → C,
      ContinuousOn r (Subtype.val '' ⋃ i, A i) ∧
      (∀ c : C, r c.val = c) ∧
      ∀ i (x : A i), r x.val.val = f i x := by
  classical
  obtain ⟨c₀, hc₀⟩ := hne
  let g : {x : E // x ∉ C} → C := fun x ↦
    if hx : ∃ i, x ∈ A i then f hx.choose ⟨x, hx.choose_spec⟩ else ⟨c₀, hc₀⟩
  have hg (i : ι) (x : {x : E // x ∉ C}) (hx : x ∈ A i) :
      g x = f i ⟨x, hx⟩ := by
    have hex : ∃ j, x ∈ A j := ⟨i, hx⟩
    simp only [g, dite_eq_left hex]
    exact hcompat hex.choose i x hex.choose_spec hx
  have hgc : ContinuousOn g (⋃ i, A i) := by
    apply hfinite.continuousOn_iUnion hclosed
    intro i
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (A i).domRestrict g = f i := by
      funext x
      exact hg i x.val x.property
    rw [heq]
    exact (f i).continuous
  let r : E → C := fun x ↦ if hx : x ∈ C then ⟨x, hx⟩ else g ⟨x, hx⟩
  have hrg (x : {x : E // x ∉ C}) : r x.val = g x := by
    simp only [r, dite_eq_right x.property]
  refine ⟨r, ?_, ?_, ?_⟩
  · apply Topology.IsInducing.subtypeVal.continuousOn_image_iff.mpr
    simpa only [Function.comp_def, hrg] using hgc
  · intro c
    simp only [r, dite_eq_left c.property]
  · intro i x
    rw [hrg]
    exact hg i x.val x.property


end HolomorphicAnosov
