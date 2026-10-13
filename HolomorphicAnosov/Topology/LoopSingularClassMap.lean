import HolomorphicAnosov.Topology.ModuleCatCycleClassNaturality
import HolomorphicAnosov.Topology.PathSingularChainMap
import HolomorphicAnosov.Topology.LoopSingularClass
import HolomorphicAnosov.Topology.IntegralSingularH1Map

noncomputable section
open CategoryTheory AlgebraicTopology
universe u
namespace HolomorphicAnosov.Topology

/-- Singular homology carries a loop's cycle class to the mapped loop's class.
Source: Hatcher, Algebraic Topology, p.111 and p.168. The chain map carries the
loop generator to the composed-loop generator, and the homology projection
commutes with this chain map. -/
theorem loopSingularClass_map {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} (α : Path x x) (g : C(X, Y)) :
    integralSingularH1Map g (loopSingularClass α) =
      loopSingularClass (α.map g.continuous) := by
  exact moduleCat_cycleClass_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) 1).map
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom g))
        (ModuleCat.of ℤ (ULift.{u} ℤ))))
    ⟨pathSingularChain α, loopSingularChain_isCycle α⟩
    ⟨pathSingularChain (α.map g.continuous), loopSingularChain_isCycle _⟩
    (pathSingularChain_map α g)
end HolomorphicAnosov.Topology
