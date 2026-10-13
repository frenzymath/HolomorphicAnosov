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

/-- The boundary is inhabited in every positive native Euclidean dimension;
its actual coordinate-unit vector is the witness used in Hatcher's good pair. -/
theorem diskBoundary_nonempty (k : ℕ) :
    ({x : {x : EuclideanSpace ℝ (Fin (k + 1)) // ‖x‖ ≤ 1} | ‖x.val‖ = 1}).Nonempty := by
  let v : EuclideanSpace ℝ (Fin (k + 1)) := PiLp.single 2 (0 : Fin (k + 1)) 1
  have hv : ‖v‖ = 1 := by simp [v]
  exact ⟨⟨v, hv.le⟩, hv⟩

end HolomorphicAnosov.Topology.Homology
