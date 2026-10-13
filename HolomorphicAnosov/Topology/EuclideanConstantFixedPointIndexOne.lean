import HolomorphicAnosov.Topology.EuclideanConstantFixedSetCompact
import HolomorphicAnosov.Topology.EuclideanConstantFixedPointIndexOneConstruction

/-!
# Normalization of the constant Euclidean fixed-point index

Source: Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood
retracts*, Topology 4 (1965), §1.4, pp. 1--2.  The displacement of a constant map
is translation by the negative constant, and translation preserves the ordered
positive local coordinate.
-/

noncomputable section
open CategoryTheory TopologicalSpace
namespace HolomorphicAnosov

/-- The canonical Euclidean fixed-point index of a constant map at an interior point
is the positive generator.  The proof is the source's translation calculation for
the singleton support orientation; the admissibility witness is the canonical
singleton compactness witness. -/
theorem euclidean_constant_fixed_point_index_one
    {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (c : EuclideanSpace ℝ (Fin n)) (hc : c ∈ U) :
    euclideanFixedPointIndex (ContinuousMap.const U c)
      (constant_fixedSet_compact c hc) = 1 := by
  exact euclidean_constant_fixed_point_index_one_construction c hc trivial

end HolomorphicAnosov
