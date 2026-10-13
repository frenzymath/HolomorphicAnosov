import HolomorphicAnosov.Topology.ModuleCatHomologyCycleRepresentative
import HolomorphicAnosov.Topology.SingularOneCycleBasedLoop
import HolomorphicAnosov.Topology.ModuleCatCycleClassEqOfBoundary
import HolomorphicAnosov.Topology.DegreeOneHurewiczHom

noncomputable section
open CategoryTheory AlgebraicTopology
universe u
namespace HolomorphicAnosov.Topology

/-- The degree-one Hurewicz homomorphism is surjective for a path-connected space.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.167. Choose a native
cycle representative of the homology class. The finite positive-path reduction,
endpoint balancing, and basepoint transport give a based loop differing from
that cycle by a two-boundary. Equality of native homology classes modulo this
boundary proves that the loop's fundamental-group class maps to the given class. -/
theorem degreeOneHurewicz_surjective {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) : Function.Surjective (degreeOneHurewicz x) := by
  intro z
  obtain ⟨a, ha⟩ := moduleCat_homology_cycle_representative ((integralSingularChains X).sc 1) z.toAdd
  let aa : (integralSingularChains X).X 1 := a.val
  have hz : ((integralSingularChains X).d 1 0) aa = 0 := by
    have h := a.property
    change ((integralSingularChains X).sc 1).g aa = 0 at h
    dsimp +instances only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor'] at h
    change ((integralSingularChains X).d 1 ((ComplexShape.down ℕ).next 1)).hom aa =
      (0 : (integralSingularChains X).X ((ComplexShape.down ℕ).next 1)) at h
    rw [ComplexShape.next_eq' (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel 1 0 from rfl)] at h
    exact h
  obtain ⟨α, c, hc⟩ := singularOneCycle_based_loop x aa hz
  have hex : ∃ c' : ((integralSingularChains X).sc 1).X₁,
      ((integralSingularChains X).sc 1).f c' = aa - pathSingularChain α := by
    dsimp +instances only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor']
    rw [ComplexShape.prev_eq' (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel 2 1 from rfl)]
    exact ⟨c, hc⟩
  obtain ⟨c', hc'⟩ := hex
  have h := moduleCat_cycleClass_eq_of_boundary ((integralSingularChains X).sc 1)
    a ⟨pathSingularChain α, loopSingularChain_isCycle α⟩ c' hc'
  refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk α), ?_⟩
  change loopSingularClass α = z.toAdd
  exact h.symm.trans ha
end HolomorphicAnosov.Topology
