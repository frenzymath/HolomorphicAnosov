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

/-- Native coordinate insertion into the next L² Euclidean model.
The final coordinate is orthogonal, as certified by the sum-of-squares identity. -/
def appendEuclidean (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    EuclideanSpace ℝ (Fin (m + 1)) := WithLp.toLp 2 (Fin.snoc x t)

end HolomorphicAnosov.Topology.Homology
