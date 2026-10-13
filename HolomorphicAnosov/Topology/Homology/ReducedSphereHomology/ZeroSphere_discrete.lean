import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ZeroSphere_finite

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

theorem zeroSphere_discrete :
    DiscreteTopology {x : EuclideanSpace ℝ (Fin 1) // ‖x‖ = 1} := by
  let : Finite {x : EuclideanSpace ℝ (Fin 1) // ‖x‖ = 1} := zeroSphere_finite
  infer_instance

end HolomorphicAnosov.Topology.Homology
