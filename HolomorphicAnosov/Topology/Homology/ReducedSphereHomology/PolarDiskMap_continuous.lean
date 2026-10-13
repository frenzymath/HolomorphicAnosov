import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.PolarDiskMap
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.AppendEuclideanLinear

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

theorem polarDiskMap_continuous (m : ℕ) : Continuous (polarDiskMap m) := by
  exact (appendEuclideanLinear m).continuous_of_finiteDimensional.comp
    (((continuous_const.mul
      (Real.continuous_sinc.comp (continuous_const.mul continuous_norm))).smul
        continuous_id).prodMk
      (Real.continuous_cos.comp (continuous_const.mul continuous_norm)))

end HolomorphicAnosov.Topology.Homology
