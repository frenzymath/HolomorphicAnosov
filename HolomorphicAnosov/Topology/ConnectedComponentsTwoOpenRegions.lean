import Mathlib.Topology.Connected.Basic

/-!
# Connected components of two disjoint open regions

This is the final component-identification step in Cairns, *An Elementary Proof
of the Jordan-Schoenflies Theorem* (1951), §5, pp.866–867. The general topological
formulation and its proof below are agent-written, using Mathlib's separation
criterion for preconnected sets and maximality of connected components.
-/

namespace HolomorphicAnosov
open Set

/-- Two nonempty connected open sets which are disjoint are precisely the connected
components of their union. Proof: every component is preconnected, so the disjoint
open cover puts it in one of the two regions. Its base point belongs to that region;
maximality gives the reverse inclusion. Conversely choose a point in either nonempty
region to realize it as a component. No separation or local connectedness assumption
on the ambient space is needed. This is the abstract final step of Cairns §5,
pp.866–867, with an agent-written proof. -/
theorem connectedComponentsIn_two_open_regions
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsConnected A) (hB : IsConnected B)
    (hAo : IsOpen A) (hBo : IsOpen B) (hAB : Disjoint A B) :
    (fun x : X ↦ connectedComponentIn (A ∪ B) x) '' (A ∪ B) = {A, B} := by
  have hcomp (x : X) (hx : x ∈ A ∪ B) :
      (connectedComponentIn (A ∪ B) x = A ∧ x ∈ A) ∨
      (connectedComponentIn (A ∪ B) x = B ∧ x ∈ B) := by
    have hxc := mem_connectedComponentIn hx
    rcases IsPreconnected.subset_or_subset hAo hBo hAB
      (connectedComponentIn_subset (A ∪ B) x)
      (isConnected_connectedComponentIn_iff.mpr hx).isPreconnected
      with hcA | hcB
    · exact Or.inl ⟨hcA.antisymm
        (hA.isPreconnected.subset_connectedComponentIn (hcA hxc) subset_union_left), hcA hxc⟩
    · exact Or.inr ⟨hcB.antisymm
        (hB.isPreconnected.subset_connectedComponentIn (hcB hxc) subset_union_right), hcB hxc⟩
  apply Subset.antisymm
  · rintro C ⟨x, hx, rfl⟩
    rcases hcomp x hx with h | h
    · simp only [h.1, mem_insert_iff, mem_singleton_iff, true_or]
    · simp only [h.1, mem_insert_iff, mem_singleton_iff, or_true]
  · intro C hC
    rcases mem_insert_iff.mp hC with hCA | hC
    · rw [hCA]
      obtain ⟨x, hx⟩ := hA.nonempty
      have hxAB : x ∈ A ∪ B := Or.inl hx
      rcases hcomp x hxAB with h | h
      · exact ⟨x, hxAB, h.1⟩
      · exact False.elim (Set.disjoint_left.mp hAB hx h.2)
    · have hCB : C = B := mem_singleton_iff.mp hC
      subst C
      obtain ⟨x, hx⟩ := hB.nonempty
      have hxAB : x ∈ A ∪ B := Or.inr hx
      rcases hcomp x hxAB with h | h
      · exact False.elim (Set.disjoint_left.mp hAB h.2 hx)
      · exact ⟨x, hxAB, h.1⟩

end HolomorphicAnosov

