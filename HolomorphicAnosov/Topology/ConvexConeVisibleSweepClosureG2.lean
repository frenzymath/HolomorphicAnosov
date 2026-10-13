import HolomorphicAnosov.Topology.ConvexConeVisibleSweepG2

open Set
namespace HolomorphicAnosov

/-- The closure of the open cone interior before the hull is the full closed
radial sweep over its compact visible front. The first-intersection lemma gives
one inclusion. Every strict radial point avoids the hull and lies in the cone;
density of the cone interior, intersected with the open hull complement, puts
it in the shadow closure. Compactness of the front makes the closed sweep
closed. Source: Cairns (1951), §3(E), p.863. -/
theorem convexCone_visible_sweep_closure_g2
    (M : ℂ) (S K : Set ℂ) (hS : S.Nonempty) (hK : Convex ℝ K)
    (hKclosed : IsClosed K) (hSK : S ⊆ K) (hM : M ∉ K)
    (hKT : K ⊆ convexHull ℝ (insert M S))
    (hTint : (interior (convexHull ℝ (insert M S))).Nonempty)
    (hMnotint : M ∉ interior (convexHull ℝ (insert M S)))
    (hfront : IsCompact {Q ∈ K | IsVisible ℝ K M Q}) :
    closure (interior (convexHull ℝ (insert M S)) \ K) =
      ⋃ Q ∈ {Q ∈ K | IsVisible ℝ K M Q}, segment ℝ M Q := by
  let V := interior (convexHull ℝ (insert M S)) \ K
  let L := {Q ∈ K | IsVisible ℝ K M Q}
  have hsub : V ⊆ ⋃ Q ∈ L, openSegment ℝ M Q := by
    intro x hx
    obtain ⟨Q,hQ,hvis,hxQ⟩ := convexCone_complement_visible_sweep_g2 M S K hS hK hKclosed
      hSK ⟨interior_subset hx.1,hx.2⟩ (fun he ↦ hMnotint (he ▸ hx.1))
    exact mem_iUnion₂.mpr ⟨Q,⟨hQ,hvis⟩,hxQ⟩
  have hback : (⋃ Q ∈ L, openSegment ℝ M Q) ⊆ closure V := by
    intro x hx
    obtain ⟨Q,hQ,hxQ⟩ := mem_iUnion₂.mp hx
    have hQM : Q ≠ M := ne_of_mem_of_not_mem hQ.1 hM
    have hxnot : x ∉ K := by
      rw [openSegment_eq_image_lineMap] at hxQ
      obtain ⟨t,ht,rfl⟩ := hxQ
      exact (isVisible_iff_lineMap hQM.symm).mp hQ.2 t ht
    have hxT : x ∈ convexHull ℝ (insert M S) :=
      (convex_convexHull ℝ _).segment_subset
        (subset_convexHull ℝ _ (mem_insert M S)) (hKT hQ.1)
        (openSegment_subset_segment ℝ _ _ hxQ)
    have hxcl : x ∈ closure (interior (convexHull ℝ (insert M S))) := by
      rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior hTint]
      exact subset_closure hxT
    exact hKclosed.isOpen_compl.closure_inter ⟨hxcl,hxnot⟩
  change closure V = ⋃ Q ∈ L, segment ℝ M Q
  rw [← halfSector_openSweep_closure_of_compact M L hfront]
  exact (closure_mono hsub).antisymm (closure_minimal hback isClosed_closure)

end HolomorphicAnosov
