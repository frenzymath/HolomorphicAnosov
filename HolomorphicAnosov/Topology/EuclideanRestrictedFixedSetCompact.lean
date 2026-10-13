import HolomorphicAnosov.Topology.EuclideanFixedPointIndexDefinition

noncomputable section
open CategoryTheory TopologicalSpace
namespace HolomorphicAnosov

/-- If a continuous map on an open Euclidean set has compact fixed set contained in a smaller open set, its restriction has compact fixed set.

Source: Dold (1965), §1.3, pp.1–2.
Proof: The ambient images of the original and restricted fixed sets coincide. Compactness is preserved by the original subtype inclusion and reflected by the embedding of the smaller open set. -/
theorem restricted_fixedSet_compact
    {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (f : C(U, EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact (euclideanFixedSet f))
    (V : Opens (EuclideanSpace ℝ (Fin n))) (hVU : V ≤ U)
    (hV : ∀ x ∈ euclideanFixedSet f, x.1 ∈ V) :
    IsCompact (euclideanFixedSet
      (⟨fun x : V ↦ f ⟨x.1, hVU x.2⟩,
        f.continuous.comp (continuous_subtype_val.subtype_mk _)⟩ :
        C(V, EuclideanSpace ℝ (Fin n)))) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have himage : Subtype.val '' euclideanFixedSet
        (⟨fun x : V ↦ f ⟨x.1, hVU x.2⟩,
          f.continuous.comp (continuous_subtype_val.subtype_mk _)⟩ :
          C(V, EuclideanSpace ℝ (Fin n))) =
      Subtype.val '' euclideanFixedSet f := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x.1, hVU x.2⟩, ?_, rfl⟩
      exact hx
    · rintro ⟨x, hx, rfl⟩
      have hxV : x.1 ∈ V := hV x hx
      refine ⟨⟨x.1, hxV⟩, ?_, rfl⟩
      exact hx
  rw [himage]
  exact hK.image continuous_subtype_val

end HolomorphicAnosov
