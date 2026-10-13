import Mathlib.Topology.Connected.Basic

/-!
# Components of a disconnected union of two preconnected sets

The component argument in Hatcher, *Algebraic Topology*, proof of Theorem 2B.3,
p.172. The proof below expands that argument for arbitrary topological spaces.
-/

namespace HolomorphicAnosov
open Set

/-- If two preconnected sets have a nonpreconnected union, each set is the component
of their union through any of its points. No openness assumption on either set is
needed. Source: the component identification in Hatcher, Theorem 2B.3 proof, p.172;
this general formulation and proof are an agent-written expansion.

Proof: maximality puts A in the component through x. If that component meets B,
maximality also puts B in that component, so the whole union is preconnected, a
contradiction. Thus the component is contained in A. The premise x∈A excludes an
empty A; if B is empty or meets A, nonpreconnectedness is impossible. -/
theorem component_of_disconnected_preconnected_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} {x : X}
    (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hunion : ¬ IsPreconnected (A ∪ B)) (hx : x ∈ A) :
    connectedComponentIn (A ∪ B) x = A := by
  have hAC : A ⊆ connectedComponentIn (A ∪ B) x :=
    hA.subset_connectedComponentIn hx subset_union_left
  apply subset_antisymm _ hAC
  intro y hy
  rcases connectedComponentIn_subset (A ∪ B) x hy with hyA | hyB
  · exact hyA
  · have hBC : B ⊆ connectedComponentIn (A ∪ B) x := by
      have hBy := hB.subset_connectedComponentIn hyB (subset_union_right : B ⊆ A ∪ B)
      rwa [← connectedComponentIn_eq hy] at hBy
    have heq : A ∪ B = connectedComponentIn (A ∪ B) x :=
      (union_subset hAC hBC).antisymm (connectedComponentIn_subset _ _)
    have hC : IsPreconnected (connectedComponentIn (A ∪ B) x) :=
      (isConnected_connectedComponentIn_iff.mpr (show x ∈ A ∪ B from Or.inl hx)).isPreconnected
    exact False.elim (hunion (heq ▸ hC))

end HolomorphicAnosov
