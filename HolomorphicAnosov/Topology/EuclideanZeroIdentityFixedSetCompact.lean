import HolomorphicAnosov.Topology.EuclideanFixedPointIndexDefinition

noncomputable section
open CategoryTheory TopologicalSpace
namespace HolomorphicAnosov

/-- The identity on the full zero-dimensional Euclidean domain has compact fixed set.

Source: Dold (1965), §1.4, pp.1–2.
Proof: The fixed set is the whole domain. Zero-dimensional Euclidean space and its full subtype are compact. -/
theorem zero_identity_fixedSet_compact :
    IsCompact (euclideanFixedSet
      (⟨Subtype.val, continuous_subtype_val⟩ : C((⊤ : Opens (EuclideanSpace ℝ (Fin 0))),
        EuclideanSpace ℝ (Fin 0)))) := by
  have hset : euclideanFixedSet
      (⟨Subtype.val, continuous_subtype_val⟩ : C((⊤ : Opens (EuclideanSpace ℝ (Fin 0))),
        EuclideanSpace ℝ (Fin 0))) = Set.univ := by
    ext x
    constructor
    · intro h
      trivial
    · intro h
      exact rfl
  rw [hset]
  exact isCompact_univ

end HolomorphicAnosov
