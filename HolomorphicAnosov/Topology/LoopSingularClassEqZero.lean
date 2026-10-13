import HolomorphicAnosov.Topology.PathSingularChain
import HolomorphicAnosov.Topology.ModuleCatCycleClassEqZero
import HolomorphicAnosov.Topology.LoopSingularClass

noncomputable section
open CategoryTheory AlgebraicTopology
universe u
namespace HolomorphicAnosov.Topology

/-- A loop has zero singular H1 class exactly when its original one-chain bounds
a singular two-chain. Source: Hatcher, Algebraic Topology, p.167, first step of
the reverse kernel inclusion. Apply the native module cycle-class zero criterion
and identify the preceding degree of the degree-one short complex with two. -/
theorem loopSingularClass_eq_zero_iff {X : Type u} [TopologicalSpace X]
    {x : X} (α : Path x x) :
    loopSingularClass α = 0 ↔
      ∃ c : (integralSingularChains X).X 2,
        ((integralSingularChains X).d 2 1) c = pathSingularChain α := by
  have h := moduleCat_cycleClass_eq_zero_iff ((integralSingularChains X).sc 1)
    ⟨pathSingularChain α, loopSingularChain_isCycle α⟩
  change loopSingularClass α = 0 ↔ _ at h
  convert h using 1
  dsimp +instances only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
    HomologicalComplex.shortComplexFunctor']
  rw [ComplexShape.prev_eq' (ComplexShape.down ℕ)
    (show (ComplexShape.down ℕ).Rel 2 1 from rfl)]
end HolomorphicAnosov.Topology
