import Mathlib.Topology.Constructions
import Mathlib.Topology.Closure

/-! An open embedding cover characterizes open sets by their preimages in the covering charts.
(Hirsch–Pugh–Shub, §7, p. 116) -/

open Set
open _root_.Topology

/-- A set is open if and only if its preimage under every map in an open embedding cover
is open. -/
theorem isOpen_iff_forall_openEmbedding_preimage_g10
    {L : Type*} [TopologicalSpace L] {ι : Type*} {D : ι → Type*}
    [∀ i, TopologicalSpace (D i)] (j : ∀ i, D i → L)
    (hj : ∀ i, IsOpenEmbedding (j i))
    (hcover : ∀ x : L, ∃ i z, j i z = x) (W : Set L) :
    IsOpen W ↔ ∀ i, IsOpen ((j i) ⁻¹' W) := by
  constructor
  · intro h i
    exact h.preimage (hj i).continuous
  · intro h
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨i, z, hz⟩ := hcover x
    refine ⟨j i '' ((j i) ⁻¹' W), Set.image_preimage_subset _ _,
      (hj i).isOpenMap _ (h i), ?_⟩
    exact ⟨z, by change j i z ∈ W; rw [hz]; exact hx, hz⟩

