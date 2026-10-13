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

set_option backward.isDefEq.respectTransparency false in
/-- The actual singular prism homotopy extends over coefficient augmentation:
the added-degree homotopy components are zero, and successor components are
Mathlib's original prism. Its degree-one equation is the original degree-zero
equation, with the additional augmentation term zero. Source: Hatcher pp.110–113. -/
def augmentedIntegralSingularChainsHomotopy {X Y : TopCat.{u}}
    {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    _root_.Homotopy (augmentedIntegralSingularChainsMap f)
      (augmentedIntegralSingularChainsMap g) where
  hom i j := match i, j with
    | i + 1, j + 1 => (H.toSSet.chainComplexMap reducedSingularIntegralCoefficients).hom i j
    | _, _ => 0
  zero i j hij := by
    cases i with
    | zero => rfl
    | succ i =>
      cases j with
      | zero => rfl
      | succ j =>
        exact (H.toSSet.chainComplexMap reducedSingularIntegralCoefficients).zero i j
          (by simpa using hij)
  comm i := by
    cases i with
    | zero =>
      rw [dNext_eq_zero _ _ (by simp),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 from rfl)]
      simp [augmentedIntegralSingularChainsMap, ChainComplex.ofHom, zero_add]
    | succ i =>
      rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel (i + 2) (i + 1) from rfl)]
      cases i with
      | zero =>
        simpa [dNext_eq_zero _ _ (show ¬ (ComplexShape.down ℕ).Rel 0
            ((ComplexShape.down ℕ).next 0) from by simp), CategoryTheory.Limits.comp_zero, zero_add,
          prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 from rfl),
          augmentedIntegralSingularChainsMap, augmentedIntegralSingularChains,
          ChainComplex.ofHom, ChainComplex.augment] using
          (H.toSSet.chainComplexMap reducedSingularIntegralCoefficients).comm 0
      | succ i =>
        simpa [dNext_eq _ (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl),
          prevD_eq _ (show (ComplexShape.down ℕ).Rel (i + 2) (i + 1) from rfl),
          augmentedIntegralSingularChainsMap, augmentedIntegralSingularChains,
          ChainComplex.ofHom, ChainComplex.augment] using
          (H.toSSet.chainComplexMap reducedSingularIntegralCoefficients).comm (i + 1)

end HolomorphicAnosov.Topology.Homology
