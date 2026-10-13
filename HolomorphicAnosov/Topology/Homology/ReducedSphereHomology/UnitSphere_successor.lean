import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundaryCollapseSphereHomeomorph
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundarySphereHomeomorph
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundary_nonempty
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundary_goodPair_guards
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.GoodPair_shift_of_acyclic
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.Disk_reduced_zero
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundaryCollarRetract
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ReducedHomologyHomeomorphIso

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- The actual disk good pair and polar quotient supply every successor
connecting isomorphism and the separate reduced-degree-zero vanishing. -/
theorem unitSphere_successor (k : ℕ) :
    IsZero (integralReducedSingularHomology
      (TopCat.of {x : EuclideanSpace ℝ (Fin (k + 1 + 1)) // ‖x‖ = 1}) 0) ∧
    ∀ q, Nonempty (integralReducedSingularHomology
      (TopCat.of {x : EuclideanSpace ℝ (Fin (k + 1 + 1)) // ‖x‖ = 1}) (q + 1) ≅
      integralReducedSingularHomology
        (TopCat.of {x : EuclideanSpace ℝ (Fin (k + 1)) // ‖x‖ = 1}) q) := by
  let E := EuclideanSpace ℝ (Fin (k + 1))
  let D := {x : E // ‖x‖ ≤ 1}
  let A : Set D := {x | ‖x.val‖ = 1}
  let V : Set D := {x | (1 : ℝ) / 2 < ‖x.val‖}
  obtain ⟨hclosed, _, hneighborhood⟩ := diskBoundary_goodPair_guards (E := E)
  have hAV : A ⊆ V := by
    intro x hx
    change (1 : ℝ) / 2 < ‖x.val‖
    change ‖x.val‖ = 1 at hx
    rw [hx]
    norm_num
  have d : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV :=
    diskBoundaryCollarRetract
  obtain ⟨hz, hs⟩ := goodPair_shift_of_acyclic (TopCat.of D) A V
    (diskBoundary_nonempty k) hclosed hAV hneighborhood d (disk_reduced_zero (E := E))
  let e := diskBoundaryCollapseSphereHomeomorph k
  refine ⟨IsZero.of_iso hz (reducedHomologyHomeomorphIso e 0).symm, ?_⟩
  intro q
  obtain ⟨δ⟩ := hs q
  exact ⟨(reducedHomologyHomeomorphIso e (q + 1)).symm ≪≫ δ ≪≫
    reducedHomologyHomeomorphIso (diskBoundarySphereHomeomorph (E := E)) q⟩

end HolomorphicAnosov.Topology.Homology
