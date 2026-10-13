import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.IntegralReducedSingularHomologyMap_homotopy

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- A genuine continuous homotopy equivalence induces an isomorphism of the
specified augmented integral singular homology modules. -/
def integralReducedHomologyIsoOfHomotopyEquiv {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y)
    (n : ℕ) : integralReducedSingularHomology (TopCat.of X) n ≅
      integralReducedSingularHomology (TopCat.of Y) n where
  hom := integralReducedSingularHomologyMap (TopCat.ofHom e.toFun) n
  inv := integralReducedSingularHomologyMap (TopCat.ofHom e.invFun) n
  hom_inv_id := by
    change (integralReducedSingularHomologyFunctor n).map (TopCat.ofHom e.toFun) ≫
      (integralReducedSingularHomologyFunctor n).map (TopCat.ofHom e.invFun) = _
    rw [← Functor.map_comp]
    obtain ⟨H⟩ := e.left_inv
    exact (integralReducedSingularHomologyMap_homotopy H n).trans
      ((integralReducedSingularHomologyFunctor n).map_id _)
  inv_hom_id := by
    change (integralReducedSingularHomologyFunctor n).map (TopCat.ofHom e.invFun) ≫
      (integralReducedSingularHomologyFunctor n).map (TopCat.ofHom e.toFun) = _
    rw [← Functor.map_comp]
    obtain ⟨H⟩ := e.right_inv
    exact (integralReducedSingularHomologyMap_homotopy H n).trans
      ((integralReducedSingularHomologyFunctor n).map_id _)

end HolomorphicAnosov.Topology.Homology
