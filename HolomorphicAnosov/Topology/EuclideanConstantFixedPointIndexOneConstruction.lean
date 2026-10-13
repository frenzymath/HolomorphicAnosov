import HolomorphicAnosov.Topology.EuclideanConstantFixedPointIndexOneTranslation

noncomputable section
open CategoryTheory TopologicalSpace
namespace HolomorphicAnosov
/-- Named Dold translation calculation for the constant Euclidean fixed-point index.
Source: Dold, Fixed point index and fixed point theorem for Euclidean neighborhood retracts,
§1.4, pp.1--2. The canonical singleton support orientation is preserved by translation. -/
theorem euclidean_constant_fixed_point_index_one_construction
    {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (c : EuclideanSpace ℝ (Fin n)) (hc : c ∈ U) (_haux : True) :
    euclideanFixedPointIndex (ContinuousMap.const U c)
      (constant_fixedSet_compact c hc) = 1 := by
  unfold euclideanFixedPointIndex
  dsimp only
  rw [euclidean_constant_displacement_positive_class c hc]
  exact (euclideanPositiveLocalCoordinate_characterization n).1
end HolomorphicAnosov
