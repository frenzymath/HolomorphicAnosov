import Mathlib.Topology.Connected.Basic

/-!
# Connected unions attached along closure points

This gives the exterior-connectivity step in Cairns, *An Elementary Proof of the
Jordan-Schoenflies Theorem* (1951), §5, pp.866–867: the two outer cells attach to
the polygon exterior through the intervening polygon arcs. The abstract closure
argument below is agent-written; Cairns does not give this general formulation.
DAG node: `topo.connected_closure_attachment_g7`.
-/

open Set

namespace HolomorphicAnosov

/-- Two connected sets have connected union if one contains a closure point of
the other. Proof: adjoin that point to the second set; this intermediate set
between the second set and its closure is connected. It meets the first set,
and their union is exactly the original union. -/
theorem isConnected_union_of_inter_closure_nonempty
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsConnected A) (hB : IsConnected B) (hAB : (A ∩ closure B).Nonempty) :
    IsConnected (A ∪ B) := by
  obtain ⟨x, hxA, hxB⟩ := hAB
  have hBx : IsConnected (insert x B) :=
    hB.subset_closure (subset_insert x B) (insert_subset hxB subset_closure)
  have h := hA.union ⟨x, hxA, mem_insert x B⟩ hBx
  simpa only [union_insert, insert_eq_of_mem (mem_union_left B hxA)] using h

/-- A connected exterior, two connected cells, and their joining seam form a
connected set when the seam lies in the exterior's closure and meets each
cell's closure. This is the topological content of the final outer-cell
recombination in Cairns §5, pp.866–867, expanded here without geometric regularity
assumptions. Proof: first adjoin the seam to the exterior, staying inside its
closure. Attach the first and second cells at their respective closure points
on the seam. The resulting union has exactly the asserted four pieces. -/
theorem isConnected_union_two_sets_and_seam
    {X : Type*} [TopologicalSpace X] {O A₁ A₂ S : Set X}
    (hO : IsConnected O) (hA₁ : IsConnected A₁) (hA₂ : IsConnected A₂)
    (hS : S ⊆ closure O)
    (h₁ : (S ∩ closure A₁).Nonempty) (h₂ : (S ∩ closure A₂).Nonempty) :
    IsConnected (O ∪ A₁ ∪ A₂ ∪ S) := by
  have hOS : IsConnected (O ∪ S) :=
    hO.subset_closure subset_union_left (union_subset subset_closure hS)
  have hOS₁ : IsConnected ((O ∪ S) ∪ A₁) :=
    isConnected_union_of_inter_closure_nonempty hOS hA₁
      (h₁.mono (inter_subset_inter_left _ subset_union_right))
  have hOS₁₂ : IsConnected (((O ∪ S) ∪ A₁) ∪ A₂) :=
    isConnected_union_of_inter_closure_nonempty hOS₁ hA₂
      (h₂.mono (inter_subset_inter_left _
        (subset_union_right.trans subset_union_left)))
  convert hOS₁₂ using 1
  ext x
  simp only [mem_union]
  tauto

end HolomorphicAnosov

