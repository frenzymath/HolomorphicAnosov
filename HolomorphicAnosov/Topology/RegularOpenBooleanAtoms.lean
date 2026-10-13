import Mathlib.Topology.Closure

/-!
# Regular-open Boolean atoms

Source: R. Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970), Lemma19,
printed p.735 (supplied PDF p.12). Closure bars omitted by text extraction are interpreted
as in the original printed lemma. All regularity predicates below are their literal
closure/interior equalities in the given topology; no separation axiom is imposed.
-/

namespace HolomorphicAnosov.Topology

universe u v w

/-- Finite regular-closed constraints define a regular-open Boolean atom.

A regular-closed set is exactly a set equal to the closure of its interior; a regular-open
set is exactly a set equal to the interior of its closure. For finite positive constraints
`K` and negative constraints `L`, the atom is the intersection of the positive interiors
minus the union of the negative sets. The conclusion includes regular-closedness of its
closure, the positive-only intersection, and regularization of every open set.

Source: Bowen (1970), Lemma19, printed p.735/PDF p.12. Complete natural-language proof:

1. For open B, specialize closure_interior_idem at B and use interior B = B to obtain
closure (interior (closure B)) = closure B. For regular-closed K, substitute
K = closure (interior K) to obtain interior K = interior (closure (interior K)). Hence
closure B is regular closed and the interior of each regular-closed set is regular open.

2. The finite intersection of the positive interiors is open, and the finite union of the
negative sets is closed, because each regular-closed set is a closure. Thus V is open and
V is contained in interior (closure V). For each positive K_a, V is contained in the closed
set K_a, so closure V is contained in K_a and interior (closure V) is contained in
interior K_a. These are the definitions and monotonicity of closure/interior and finite
set operations. With no negative constraints this already gives the positive-only equality.

3. For each negative L_b, interior L_b is open and disjoint from V. Disjoint.closure_right
makes it disjoint from closure V. Were x in interior (closure V) and L_b, then
L_b = closure (interior L_b) and the open neighborhood interior (closure V) of x would meet
interior L_b, contradicting that disjointness. Hence interior (closure V) misses all L_b
and is contained in V, proving equality. Taking closures gives regular-closedness of
closure V. Applying the first step to an arbitrary open B gives regular-closedness of
closure B and regular-openness of interior (closure B).

Empty positive families give the whole space before the negative constraints. Empty
negative families give the positive-only intersection. When both families are empty the
atom is the whole space. Empty X, empty V and empty B satisfy the same equalities. The
argument does not require Hausdorffness, nonempty families, distinct constraints, or
nonempty interior of an individual regular-closed set.
-/
theorem manningBowen_regularOpen_booleanAtoms
    {X : Type u} [TopologicalSpace X]
    {ι : Type v} {κ : Type w} [Finite ι] [Finite κ]
    (K : ι → Set X) (L : κ → Set X)
    (hK : ∀ a, K a = closure (interior (K a)))
    (hL : ∀ b, L b = closure (interior (L b))) :
    let P : Set X := ⋂ a, interior (K a)
    let V : Set X := P \ (⋃ b, L b)
    IsOpen V ∧
      interior (closure V) = V ∧
      closure (interior (closure V)) = closure V ∧
      interior (closure P) = P ∧
      ∀ B : Set X, IsOpen B →
        closure (interior (closure B)) = closure B ∧
          interior (closure (interior (closure B))) = interior (closure B) := by
  classical
  dsimp only
  let P : Set X := ⋂ a, interior (K a)
  let V : Set X := P \ (⋃ b, L b)
  have hPopen : IsOpen P := by
    exact isOpen_iInter_of_finite (fun a ↦ isOpen_interior)
  have hLclosed : IsClosed (⋃ b, L b) := by
    apply isClosed_iUnion_of_finite
    intro b
    rw [hL b]
    exact isClosed_closure
  have hVopen : IsOpen V := hPopen.sdiff hLclosed
  have hVsubP : V ⊆ P := Set.sdiff_subset
  have hPsubK : ∀ a, P ⊆ K a := fun a x hx ↦
    interior_subset (Set.mem_iInter.mp hx a)
  have hKclosed : ∀ a, IsClosed (K a) := by
    intro a
    rw [hK a]
    exact isClosed_closure
  have hclVsubP : interior (closure V) ⊆ P := by
    intro x hx
    exact Set.mem_iInter.mpr (fun a ↦
      interior_mono (closure_minimal (hVsubP.trans (hPsubK a)) (hKclosed a)) hx)
  have hVint : V ⊆ interior (closure V) := hVopen.subset_interior_closure
  have hneg : ∀ b, interior (closure V) ⊆ (L b)ᶜ := by
    intro b x hxU hxL
    have hdisj : Disjoint V (interior (L b)) := by
      rw [Set.disjoint_left]
      intro y hyV hyI
      exact hyV.2 (Set.mem_iUnion.2 ⟨b, interior_subset hyI⟩)
    have hdisj' : Disjoint (closure V) (interior (L b)) :=
      hdisj.closure_left isOpen_interior
    have hdisj'' : Disjoint (interior (closure V)) (closure (interior (L b))) :=
      (hdisj'.mono_left interior_subset).closure_right isOpen_interior
    have : x ∉ closure (interior (L b)) := Set.disjoint_left.1 hdisj'' hxU
    exact this (by rw [← hL b]; exact hxL)
  have hclVeq : interior (closure V) = V := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨hclVsubP hx, by
        intro hxneg
        rcases Set.mem_iUnion.1 hxneg with ⟨b, hxb⟩
        exact hneg b hx hxb⟩
    · exact hVint
  have hPcl : interior (closure P) = P := by
    apply Set.Subset.antisymm
    · intro x hx
      exact Set.mem_iInter.mpr (fun a ↦
        interior_mono (closure_minimal (hPsubK a) (hKclosed a)) hx)
    · exact hPopen.subset_interior_closure
  refine ⟨hVopen, hclVeq, ?_, hPcl, ?_⟩
  · rw [hclVeq]
  · intro B hB
    constructor
    · simpa only [hB.interior_eq] using (closure_interior_idem (s := B))
    · simpa only [hB.interior_eq] using (interior_closure_idem (s := B))


end HolomorphicAnosov.Topology
