import HolomorphicAnosov.Topology.EuclideanFixedPointIndexDefinition

noncomputable section
open CategoryTheory TopologicalSpace
namespace HolomorphicAnosov

/-- For a continuous Euclidean map with compact fixed set, a finite disjoint open family covering all fixed points has compact fixed set in each restriction.
Source: Dold (1965), §1.5, pp.1–2.
Proof: For one component, let O be the union of all the other open components. Its restricted ambient fixed set equals the original compact fixed set intersected with the closed complement of O. Disjointness gives one inclusion and the covering condition gives the reverse. Compactness of the intersection and the subtype embedding prove the claim. -/
theorem disjoint_restricted_fixedSet_compact
    {n k : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (f : C(U, EuclideanSpace ℝ (Fin n))) (hK : IsCompact (euclideanFixedSet f))
    (V : Fin k → Opens (EuclideanSpace ℝ (Fin n))) (hVU : ∀ i, V i ≤ U)
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i : Set (EuclideanSpace ℝ (Fin n)))
      (V j : Set (EuclideanSpace ℝ (Fin n))))
    (hcover : ∀ x ∈ euclideanFixedSet f, ∃ i, x.1 ∈ V i) (i : Fin k) :
    IsCompact (euclideanFixedSet
      (⟨fun x : V i ↦ f ⟨x.1, hVU i x.2⟩,
        f.continuous.comp (continuous_subtype_val.subtype_mk _)⟩ :
        C(V i, EuclideanSpace ℝ (Fin n)))) := by
  let O : Set (EuclideanSpace ℝ (Fin n)) := ⋃ j, ⋃ (_ : j ≠ i), (V j : Set _)
  have hO : IsOpen O := isOpen_iUnion fun j ↦
    isOpen_iUnion fun _ ↦ (V j).isOpen
  have hcompact := (hK.image continuous_subtype_val).inter_right hO.isClosed_compl
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have himage : Subtype.val '' euclideanFixedSet
        (⟨fun x : V i ↦ f ⟨x.1, hVU i x.2⟩,
          f.continuous.comp (continuous_subtype_val.subtype_mk _)⟩ :
          C(V i, EuclideanSpace ℝ (Fin n))) =
      (Subtype.val '' euclideanFixedSet f) ∩ Oᶜ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨⟨x.1, hVU i x.2⟩, hx, rfl⟩, ?_⟩
      intro hmem
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨hji, hj⟩ := Set.mem_iUnion.mp hj
      exact Set.disjoint_left.mp (hdisj j i hji) hj x.property
    · rintro ⟨⟨x, hx, rfl⟩, hnot⟩
      obtain ⟨j, hj⟩ := hcover x hx
      have hji : j = i := by
        by_contra hne
        exact hnot (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hne, hj⟩⟩)
      subst j
      exact ⟨⟨x.1, hj⟩, hx, rfl⟩
  rw [himage]
  exact hcompact

end HolomorphicAnosov
