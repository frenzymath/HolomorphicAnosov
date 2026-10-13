import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.IntegralReducedPositiveOrdinaryIso
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiscreteReducedH0SumKernel

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- The reduced complex of a point is acyclic, including degree zero:
its point-indexed augmentation is the one-summand coproduct isomorphism. -/
theorem unique_reduced_zero (X : TopCat.{0}) [Unique X] (q : ℕ) :
    IsZero (integralReducedSingularHomology X q) := by
  have : DiscreteTopology X := inferInstance
  cases q with
  | zero =>
    let e := coproductUniqueIso (fun _ : X ↦ reducedSingularIntegralCoefficients)
    have he : Sigma.desc (fun _ : X ↦ 𝟙 reducedSingularIntegralCoefficients) = e.hom := by
      apply Sigma.hom_ext
      intro x
      simp [e]
    have : IsIso (Sigma.desc (fun _ : X ↦ 𝟙 reducedSingularIntegralCoefficients)) := by
      rw [he]
      infer_instance
    exact IsZero.of_iso (isZero_kernel_of_mono _)
      (discreteReducedH0SumKernel X)
  | succ q =>
    apply IsZero.of_iso ?_ (integralReducedPositiveOrdinaryIso X q)
    exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℤ) (q + 1) reducedSingularIntegralCoefficients X (by omega)

end HolomorphicAnosov.Topology.Homology
