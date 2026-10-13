import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.AppendEuclidean

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- The radial disk-to-sphere formula is written with sinc at the center,
so its first component is continuous without division by a vanishing norm. -/
def polarDiskMap (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  appendEuclidean m ((Real.pi * Real.sinc (Real.pi * ‖x‖)) • x)
    (Real.cos (Real.pi * ‖x‖))

end HolomorphicAnosov.Topology.Homology
