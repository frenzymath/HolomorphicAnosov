import HolomorphicAnosov.Topology.PathSingularChain
import HolomorphicAnosov.Topology.PathSingularChainBoundaryCoefficients
import Mathlib.Algebra.BigOperators.Group.List.Basic

noncomputable section
open CategoryTheory
universe u
namespace HolomorphicAnosov.Topology

/-- A finite positive path sum has boundary coefficients given by the sum of
its targets minus the sum of its sources.
Source: Hatcher, Algebraic Topology, p.167, endpoint balance of a cycle.
Apply linearity to the finite sum and use the target-minus-source boundary
formula for each individual path; collect the two endpoint sums. -/
theorem pathList_boundary_coefficients {X : Type u} [TopologicalSpace X]
    (l : List (Σ x y : X, Path x y)) :
    (singularChainGeneratorIso (TopCat.of X) 0).hom
      (((integralSingularChains X).d 1 0)
        ((l.map (fun p ↦ pathSingularChain p.2.2)).sum)) =
      (l.map (fun p ↦ Finsupp.single (ContinuousMap.const _ p.2.1) (1 : ULift.{u} ℤ))).sum -
        (l.map (fun p ↦ Finsupp.single (ContinuousMap.const _ p.1) (1 : ULift.{u} ℤ))).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := pathSingularChain_boundary_coefficients (X := X) p.2.2
    simp only [List.map_cons, List.sum_cons, map_add, hp, ih]
    abel
end HolomorphicAnosov.Topology
