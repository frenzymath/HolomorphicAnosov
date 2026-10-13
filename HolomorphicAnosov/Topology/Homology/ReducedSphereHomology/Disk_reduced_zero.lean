import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.IntegralReducedHomologyIsoOfHomotopyEquiv
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.Unique_reduced_zero

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- The SAME native Euclidean closed disk is convex, and its radial
contraction is the source contractibility proof. The actual augmented prism
transports its homology to the point complex just computed. -/
theorem disk_reduced_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℕ) : IsZero (integralReducedSingularHomology
      (TopCat.of {x : E // ‖x‖ ≤ 1}) q) := by
  let B : Set E := Metric.closedBall 0 1
  let : ContractibleSpace B := (convex_closedBall (0 : E) 1).contractibleSpace
    ⟨0, by simp⟩
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit B
  have h := IsZero.of_iso (unique_reduced_zero (TopCat.of Unit) q)
    (integralReducedHomologyIsoOfHomotopyEquiv e q)
  have hB : B = {x : E | ‖x‖ ≤ 1} := by
    ext x
    simp only [B, Metric.mem_closedBall, dist_eq_norm, sub_zero, Set.mem_ofPred_eq]
  rw [hB] at h
  exact h

end HolomorphicAnosov.Topology.Homology
