import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- On a totally disconnected native space both faces of every singular
1-simplex are the same point. The actual ordinary first differential is zero;
this is Hatcher's two-point base calculation through Mathlib's constant-chain
isomorphism. -/
theorem disconnected_first_boundary_zero (X : TopCat)
    [TotallyDisconnectedSpace X] :
    ((TopCat.toSSet.obj X).chainComplex reducedSingularIntegralCoefficients).d 1 0 = 0 := by
  let e := AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
    (ModuleCat ℤ) reducedSingularIntegralCoefficients X
  have h := e.hom.comm 1 0
  have hz : (ChainComplex.alternatingConst.obj
      (∐ fun _ : X ↦ reducedSingularIntegralCoefficients)).d 1 0 = 0 := by
    simp [ChainComplex.alternatingConst, HomologicalComplex.alternatingConst]
    rfl
  rw [hz, CategoryTheory.Limits.comp_zero] at h
  have hh : (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      reducedSingularIntegralCoefficients).obj X).d 1 0 = 0 := by
    apply (cancel_mono (e.hom.f 0)).mp
    rw [CategoryTheory.Limits.zero_comp]
    exact h.symm
  exact hh

end HolomorphicAnosov.Topology.Homology
