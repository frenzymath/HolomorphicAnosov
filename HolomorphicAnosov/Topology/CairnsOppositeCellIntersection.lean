import Mathlib.Topology.Closure

namespace HolomorphicAnosov
open Set

/-- Closed cells lying in disjoint open sectors meet only on the common base,
provided the sectors' remaining boundary arcs meet only on that base. A point
in both sector closures is on both frontiers; intersect their frontier bounds.
The reverse containment is supplied by the cells' base edges. -/
theorem opposite_cells_closure_intersection
    {X : Type*} [TopologicalSpace X]
    (U V P Q B L M : Set X) (hP : IsOpen P) (hQ : IsOpen Q)
    (hdisj : Disjoint P Q) (hU : U ⊆ P) (hV : V ⊆ Q)
    (hPfront : frontier P ⊆ B ∪ L) (hQfront : frontier Q ⊆ B ∪ M)
    (hLM : L ∩ M ⊆ B) (hBU : B ⊆ closure U) (hBV : B ⊆ closure V) :
    closure U ∩ closure V = B := by
  apply Subset.antisymm
  · intro x hx
    have hxP := closure_mono hU hx.1
    have hxQ := closure_mono hV hx.2
    have hclP : closure P ⊆ Qᶜ := closure_minimal
      (fun z hz ↦ Set.disjoint_left.mp hdisj hz) hQ.isClosed_compl
    have hclQ : closure Q ⊆ Pᶜ := closure_minimal
      (fun z hz ↦ Set.disjoint_right.mp hdisj hz) hP.isClosed_compl
    have hxPf : x ∈ frontier P := by rw [hP.frontier_eq];exact ⟨hxP,hclQ hxQ⟩
    have hxQf : x ∈ frontier Q := by rw [hQ.frontier_eq];exact ⟨hxQ,hclP hxP⟩
    rcases hPfront hxPf with hxB | hxL
    · exact hxB
    rcases hQfront hxQf with hxB | hxM
    · exact hxB
    · exact hLM ⟨hxL,hxM⟩
  · exact fun x hx ↦ ⟨hBU hx,hBV hx⟩

end HolomorphicAnosov
