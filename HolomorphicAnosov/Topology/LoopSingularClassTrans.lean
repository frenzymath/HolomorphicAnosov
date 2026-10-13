import HolomorphicAnosov.Topology.LoopSingularClass
import HolomorphicAnosov.Topology.PathTransSingularBoundary
import HolomorphicAnosov.Topology.ModuleCatCycleClassEqOfBoundary

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory AlgebraicTopology
universe u
namespace HolomorphicAnosov.Topology

/-- Concatenation of based loops adds their native singular homology classes.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.166. The concatenation
triangle bounds the sum of the loop chains minus the concatenation chain.
The native homology projection is linear, so equality modulo this boundary
gives the displayed addition law. -/
theorem loopSingularClass_trans {X : Type u} [TopologicalSpace X]
    {x : X} (α β : Path x x) :
    loopSingularClass (α.trans β) = loopSingularClass α + loopSingularClass β := by
  obtain ⟨c, hc⟩ := pathTrans_singular_boundary α β
  have hex : ∃ c' : ((integralSingularChains X).sc 1).X₁,
      ((integralSingularChains X).sc 1).f c' =
        pathSingularChain α + pathSingularChain β - pathSingularChain (α.trans β) := by
    dsimp +instances only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor']
    rw [ComplexShape.prev_eq' (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel 2 1 from rfl)]
    exact ⟨c, hc⟩
  obtain ⟨c', hc'⟩ := hex
  let a : LinearMap.ker ((integralSingularChains X).sc 1).g.hom :=
    ⟨pathSingularChain α, loopSingularChain_isCycle α⟩
  let b : LinearMap.ker ((integralSingularChains X).sc 1).g.hom :=
    ⟨pathSingularChain β, loopSingularChain_isCycle β⟩
  have h := moduleCat_cycleClass_eq_of_boundary ((integralSingularChains X).sc 1)
    (a + b) ⟨pathSingularChain (α.trans β), loopSingularChain_isCycle _⟩ c' hc'
  change _ = loopSingularClass (α.trans β) at h
  change ((integralSingularChains X).sc 1).homologyπ.hom
    (((integralSingularChains X).sc 1).moduleCatCyclesIso.inv.hom
      ((a : ((integralSingularChains X).sc 1).moduleCatLeftHomologyData.K) + b)) = _ at h
  have hi := ((integralSingularChains X).sc 1).moduleCatCyclesIso.inv.hom.map_add a b
  have hp := ((integralSingularChains X).sc 1).homologyπ.hom.map_add
    (((integralSingularChains X).sc 1).moduleCatCyclesIso.inv a)
    (((integralSingularChains X).sc 1).moduleCatCyclesIso.inv b)
  exact h.symm.trans ((congrArg
    (fun z ↦ ((integralSingularChains X).sc 1).homologyπ.hom z) hi).trans hp)

end HolomorphicAnosov.Topology
