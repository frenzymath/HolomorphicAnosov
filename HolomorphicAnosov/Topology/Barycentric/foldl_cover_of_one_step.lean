import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Module

/-!
# Iterating a one-step set cover

Source context: Hatcher, *Algebraic Topology*, proof of Proposition 2.21(1), pp. 119–121,
iterates barycentric subdivision. The general set-theoretic list-fold lemma below is an
elementary induction abstracted from that application, rather than a statement quoted from
Hatcher. DAG node: `topo.barycentric_foldl_cover_of_one_step_g16`.
-/

namespace HolomorphicAnosov.BarycentricGeometry

open Set

universe u

/-- If each set is covered exactly by the sets of its children, it is covered exactly by the
sets reached along all lists of children of any prescribed finite length.

Source context: Hatcher, *Algebraic Topology*, proof of Proposition 2.21(1), pp. 119–121,
and the finite-depth step in `topo.barycentric_subdivision_coverage`. This general formulation
and its elementary induction are agent-written; no real module or finiteness assumption on
the branching type is needed.

Proof: Induct on the list length, keeping the starting state arbitrary. At length zero the
only list is empty and its fold leaves the state unchanged. At successor length, first use
the one-step cover and then the induction hypothesis for each child. Prepending the first
child index to a list of the smaller length gives a list of the required successor length.
Conversely, every list of successor length is a head followed by a list of the smaller length;
the induction hypothesis for that first child and then the one-step cover give containment
in the original set. The defining equation for the left fold identifies these endpoints.
-/
theorem foldl_cover_of_one_step
    {S I E : Type*} (C : S → Set E) (child : S → I → S)
    (hstep : ∀ s, C s = ⋃ i, C (child s i)) (s : S) :
    ∀ r : ℕ, C s =
      ⋃ p : {p : List I // p.length = r}, C (p.val.foldl child s) := by
  intro r
  induction r generalizing s with
  | zero =>
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨⟨[], rfl⟩, hx⟩
    · intro hx
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
      have hnil : p.val = [] := List.length_eq_zero_iff.mp p.property
      simpa [hnil] using hp
  | succ r ih =>
    rw [hstep s]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      rw [ih (child s i)] at hi
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hi
      exact Set.mem_iUnion.mpr ⟨⟨i :: p.val, by simp [p.property]⟩, hp⟩
    · intro hx
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
      obtain ⟨ps, hlen⟩ := p
      cases ps with
      | nil => simp at hlen
      | cons i ps =>
        apply Set.mem_iUnion.mpr
        refine ⟨i, ?_⟩
        rw [ih (child s i)]
        apply Set.mem_iUnion.mpr
        exact ⟨⟨ps, by simpa using hlen⟩, hp⟩

end HolomorphicAnosov.BarycentricGeometry

