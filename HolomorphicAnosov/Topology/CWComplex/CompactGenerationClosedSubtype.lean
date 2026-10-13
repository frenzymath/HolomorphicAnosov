import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

/-! Source: Fritsch–Piccinini, Cellular Structures in Topology, Appendix A.1 p.242,
closed-subspace inheritance of the k-space property. The compact-test proof below expands the
omitted argument. DAG: topo.closed_subtype_compact_generation_g8. -/

namespace HolomorphicAnosov.Topology.CWComplex

universe u

/--
A closed subtype of a Hausdorff compactly generated space is compactly
generated in its induced topology.

Source: Fritsch–Piccinini, *Cellular Structures in Topology*, Appendix A.1,
p. 242, closed-subspace inheritance assertion (1). The proof below is an
agent-written expansion of its omitted compact-test argument in the Hausdorff case.

For a compact test set `K` in the ambient space, the closed embedding of the
subtype has compact preimage. Intersecting that preimage with a candidate
closed set gives a compact set; its image in the Hausdorff ambient space is
closed. The ambient compact-generation criterion then shows that the image of
the candidate set is closed, and the induced-topology characterization pulls
this back to the subtype.
-/
theorem compactlyGeneratedSpace_of_closed_subtype
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactlyGeneratedSpace X]
    {A : Set X} (hA : IsClosed A) : CompactlyGeneratedSpace A := by
  apply compactlyGeneratedSpace_of_isClosed_of_t2
  intro s hs
  have hclosed : IsClosed ((Subtype.val : A → X) '' s) := by
    apply CompactlyGeneratedSpace.isClosed (X := X)
    intro K hK
    rw [← Set.image_inter_preimage]
    have hpre : IsCompact (Subtype.val ⁻¹' K) :=
      hA.isClosedEmbedding_subtypeVal.isCompact_preimage hK
    have hsk : IsCompact (s ∩ Subtype.val ⁻¹' K) :=
      hpre.of_isClosed_subset (hs (K := Subtype.val ⁻¹' K) hpre) Set.inter_subset_right
    exact hsk.image continuous_subtype_val |>.isClosed
  rw [isClosed_induced_iff]
  exact ⟨(Subtype.val : A → X) '' s, hclosed,
    Set.preimage_image_eq s Subtype.val_injective⟩

end HolomorphicAnosov.Topology.CWComplex

