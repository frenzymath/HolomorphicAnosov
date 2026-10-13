import HolomorphicAnosov.Topology.LoopSingularClass
import HolomorphicAnosov.Topology.ConstantPathSingularBoundary
import HolomorphicAnosov.Topology.ModuleCatCycleClassEqOfBoundary

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory AlgebraicTopology
universe u
namespace HolomorphicAnosov.Topology

/-- The constant based loop has zero native singular homology class.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.166.
The constant singular triangle has the constant loop as its boundary, so the
native cycle-to-homology projection identifies that loop cycle with zero. -/
theorem loopSingularClass_refl {X : Type u} [TopologicalSpace X] (x : X) :
    loopSingularClass (Path.refl x) = 0 := by
  obtain ⟨c, hc⟩ := constantPath_singular_boundary x
  have hex : ∃ c' : ((integralSingularChains X).sc 1).X₁,
      ((integralSingularChains X).sc 1).f c' = pathSingularChain (Path.refl x) := by
    dsimp +instances only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor']
    rw [ComplexShape.prev_eq' (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel 2 1 from rfl)]
    exact ⟨c, hc⟩
  obtain ⟨c', hc'⟩ := hex
  have h := moduleCat_cycleClass_eq_of_boundary ((integralSingularChains X).sc 1)
    ⟨pathSingularChain (Path.refl x), loopSingularChain_isCycle _⟩ 0 c' (by change _ = pathSingularChain (Path.refl x) - 0; rw [sub_zero]; exact hc')
  change loopSingularClass (Path.refl x) =
    ((integralSingularChains X).sc 1).homologyπ
      (((integralSingularChains X).sc 1).moduleCatCyclesIso.inv 0) at h
  rw [map_zero, map_zero] at h
  exact h

end HolomorphicAnosov.Topology
