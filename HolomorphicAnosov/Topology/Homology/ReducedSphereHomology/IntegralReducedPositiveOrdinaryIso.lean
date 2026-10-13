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
/-- In positive degree the three actual augmented chain objects and maps are
those of ordinary singular chains, shifted once. This is the same chain-level
comparison used in the dimension-invariance source argument. -/
def integralReducedPositiveOrdinaryIso (X : TopCat.{u}) (n : ℕ) :
    integralReducedSingularHomology X (n + 1) ≅
      ((TopCat.toSSet.obj X).chainComplex reducedSingularIntegralCoefficients).homology
        (n + 1) := by
  let A := augmentedIntegralSingularChains X
  let C := (TopCat.toSSet.obj X).chainComplex reducedSingularIntegralCoefficients
  exact A.homologyIsoSc' (n + 3) (n + 2) (n + 1) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [A,
        augmentedIntegralSingularChains, Category.id_comp, Category.comp_id])
        (by simp [A, augmentedIntegralSingularChains, Category.id_comp, Category.comp_id])) ≪≫
    (C.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).symm

end HolomorphicAnosov.Topology.Homology
