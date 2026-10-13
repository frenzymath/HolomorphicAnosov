import HolomorphicAnosov.Topology.EuclideanFixedPointIndexDefinition

noncomputable section
open CategoryTheory TopologicalSpace
namespace HolomorphicAnosov

/-- The fixed set of a constant map with value in its open Euclidean domain is compact.

Source: Dold (1965), §1.4, pp.1–2.
Proof: The fixed set is the singleton consisting of the constant value, regarded as a point of the domain. Singletons are compact. -/
theorem constant_fixedSet_compact
    {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (c : EuclideanSpace ℝ (Fin n)) (hc : c ∈ U) :
    IsCompact (euclideanFixedSet (ContinuousMap.const U c)) := by
  have hset : euclideanFixedSet (ContinuousMap.const U c) = {⟨c, hc⟩} := by
    ext x
    constructor
    · intro h
      apply Subtype.ext
      exact h.symm
    · intro h
      rw [Set.mem_singleton_iff] at h
      subst x
      rfl
  rw [hset]
  exact isCompact_singleton

end HolomorphicAnosov
