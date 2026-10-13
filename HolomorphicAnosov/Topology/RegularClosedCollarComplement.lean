import Mathlib.Topology.Closure

/-!
# Complementary regular-closed factors inside an open collar

Source: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970), p.735,
the construction of the complementary factors immediately after Lemma 19.
DAG node: `topo.regular_closed_collar_complement_g18`.
-/

namespace HolomorphicAnosov.Topology

open Set

/-- The closure of the collar complement of a regular-closed set is regular closed.
Its interior misses the original closed factor, and inside the collar its interior
is precisely the complement of that factor. The two closed factors cover the collar,
and the complementary factor stays in the closure of the collar.

Source: Bowen (1970), p.735, complementary-factor construction following Lemma 19.
The difference is open because the original factor is closed. The closure of an open
set is regular closed by closure-interior idempotence. Its closure misses the interior
of the original factor; taking the interior on one side and closure on the other shows
separation from the whole original factor. Openness gives the reverse inclusion in the
interior identity. Coverage and the collar bound follow from closure monotonicity.
No separation axiom, nonemptiness, or containment of the original factor in the collar
is needed. Apply this in a plaque subtype to obtain Bowen's relative closures.
-/
theorem regularClosed_collar_complement {X : Type*} [TopologicalSpace X]
    (C E : Set X) (hC : C = closure (interior C)) (hE : IsOpen E) :
    let D := closure (E \ C)
    D = closure (interior D) ∧
      Disjoint (interior D) C ∧
      interior D ∩ E = E \ C ∧
      E ⊆ C ∪ D ∧ D ⊆ closure E := by
  dsimp only
  have hCclosed : IsClosed C := hC ▸ isClosed_closure
  have hopen : IsOpen (E \ C) := hE.sdiff hCclosed
  have hd : Disjoint (E \ C) (interior C) := by
    rw [Set.disjoint_left]
    exact fun _ hx hy ↦ hx.2 (interior_subset hy)
  have hsep : Disjoint (interior (closure (E \ C))) C := by
    simpa only [← hC] using
      ((hd.closure_left isOpen_interior).mono_left interior_subset).closure_right
      isOpen_interior
  refine ⟨?_, hsep, ?_, ?_, closure_mono Set.sdiff_subset⟩
  · simpa only [hopen.interior_eq] using (closure_interior_idem (s := E \ C)).symm
  · apply Set.Subset.antisymm
    · exact fun _ hx ↦ ⟨hx.2, Set.disjoint_left.mp hsep hx.1⟩
    · exact fun _ hx ↦ ⟨hopen.subset_interior_closure hx, hx.1⟩
  · intro x hx
    by_cases hc : x ∈ C
    · exact Or.inl hc
    · exact Or.inr (subset_closure ⟨hx, hc⟩)

end HolomorphicAnosov.Topology
