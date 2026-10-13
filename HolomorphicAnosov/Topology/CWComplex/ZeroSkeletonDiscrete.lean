import Mathlib.Topology.CWComplex.Classical.Subcomplex

open Set
namespace HolomorphicAnosov.Topology.CWComplex

universe u

/-- The zero skeleton of an absolute CW complex is discrete in its induced topology.

Source: Fritsch–Piccinini, *Cellular Structures in Topology*, §1.2, printed p.22,
CW filtration condition (0) and the base case of Proposition 1.2.1 (pp.22–23).
The native characteristic-map interface realizes this condition by its weak-topology
criterion: a subset of the zero skeleton meets every inherited closed cell in a finite
set, since the skeleton has only zero-dimensional cells and a zero-dimensional disk
is a singleton. These intersections are closed in the Hausdorff ambient space, so the
subset is closed there. Pulling it back to the skeleton proves every subset closed,
and hence proves discreteness without changing the topology. This also handles an
empty zero skeleton or an arbitrary infinite zero-cell family.
-/
theorem zero_skeleton_discrete
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [_root_.Topology.CWComplex C] :
    DiscreteTopology ↥(_root_.Topology.RelCWComplex.skeleton C 0 : Set X) := by
  let S : Set X := _root_.Topology.RelCWComplex.skeleton C 0
  apply discreteTopology_iff_forall_isClosed.mpr
  intro A
  have hclosed : IsClosed (Subtype.val '' A : Set X) := by
    apply (_root_.Topology.CWComplex.closed S _ (by
      rintro _ ⟨x, hx, rfl⟩
      exact x.property)).mpr
    intro n i
    have hn : n = 0 := by
      have hi := i.property
      change i.val ∈ (_root_.Topology.RelCWComplex.skeletonLT C (0 + 1)).I n at hi
      have hi' : (n : ℕ∞) < 0 + 1 := by
        simpa only [_root_.Topology.RelCWComplex.skeletonLT_I, Set.mem_ofPred_eq] using hi
      simpa using hi'
    subst n
    have hfin : (_root_.Topology.RelCWComplex.closedCell (C := S) 0 i).Finite := by
      apply Set.Finite.image
      exact Set.toFinite _
    exact (hfin.subset inter_subset_right).isClosed
  have heq : (fun x : S ↦ x.val) ⁻¹' (Subtype.val '' A : Set X) = A :=
    Set.preimage_image_eq _ Subtype.val_injective
  rw [← heq]
  exact hclosed.preimage continuous_subtype_val

end HolomorphicAnosov.Topology.CWComplex
