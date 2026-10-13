import Mathlib.Topology.Connected.Basic

/-! DAG node: `topo.component_connection_frontier_contacts_g10`. -/

open Set
namespace HolomorphicAnosov

/-- Two connected sets whose frontiers touch one connected set belong to the
same component of any open obstacle complement containing all three sets.
Agent expansion of Cairns (1951), Lemma 3.1 corollary, p.862. Adjoin each contact
point to its region; the enlarged region remains connected because the contact
is in its closure. Unite both enlarged regions with the connecting set, using
those two contact points, and apply maximality of the connected component. -/
theorem component_connection_of_frontier_contacts
    {X : Type*} [TopologicalSpace X] {B₁ B₂ T U : Set X}
    (h₁ : IsPreconnected B₁) (h₂ : IsPreconnected B₂) (hT : IsPreconnected T)
    (h₁U : B₁ ⊆ U) (h₂U : B₂ ⊆ U) (hTU : T ⊆ U)
    {x₁ x₂ : X} (hx₁ : x₁ ∈ B₁) (hx₂ : x₂ ∈ B₂)
    (hc₁ : (frontier B₁ ∩ T).Nonempty) (hc₂ : (frontier B₂ ∩ T).Nonempty) :
    x₂ ∈ connectedComponentIn U x₁ := by
  obtain ⟨y₁, hy₁, hy₁T⟩ := hc₁
  obtain ⟨y₂, hy₂, hy₂T⟩ := hc₂
  have hi₁ : IsPreconnected (insert y₁ B₁) := h₁.subset_closure (subset_insert _ _)
    (insert_subset (frontier_subset_closure hy₁) subset_closure)
  have hi₂ : IsPreconnected (insert y₂ B₂) := h₂.subset_closure (subset_insert _ _)
    (insert_subset (frontier_subset_closure hy₂) subset_closure)
  have hc : IsPreconnected ((insert y₁ B₁ ∪ T) ∪ insert y₂ B₂) :=
    (hi₁.union y₁ (mem_insert _ _) hy₁T hT).union y₂
      (Or.inr hy₂T) (mem_insert _ _) hi₂
  apply hc.subset_connectedComponentIn (Or.inl (Or.inl (mem_insert_of_mem _ hx₁)))
    (union_subset (union_subset (insert_subset (hTU hy₁T) h₁U) hTU)
      (insert_subset (hTU hy₂T) h₂U))
  exact Or.inr (mem_insert_of_mem _ hx₂)

end HolomorphicAnosov

