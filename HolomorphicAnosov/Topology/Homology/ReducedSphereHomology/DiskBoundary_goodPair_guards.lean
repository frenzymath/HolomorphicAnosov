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

/-- The collar used in the SOURCE disk-pair induction is genuinely relatively
open, and its boundary is closed in the original disk. -/
theorem diskBoundary_goodPair_guards {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    let D := {x : E // ‖x‖ ≤ 1}
    let A : Set D := {x | ‖x.val‖ = 1}
    let V : Set D := {x | (1 : ℝ) / 2 < ‖x.val‖}
    IsClosed A ∧ IsOpen V ∧ A ⊆ interior V := by
  dsimp only
  have hn : Continuous (fun x : {x : E // ‖x‖ ≤ 1} ↦ ‖x.val‖) :=
    continuous_subtype_val.norm
  have ho : IsOpen {x : {x : E // ‖x‖ ≤ 1} | (1 : ℝ) / 2 < ‖x.val‖} :=
    isOpen_lt continuous_const hn
  refine ⟨isClosed_eq hn continuous_const, ho, ?_⟩
  rw [ho.interior_eq]
  intro x hx
  change (1 : ℝ) / 2 < ‖x.val‖
  rw [hx]
  norm_num

end HolomorphicAnosov.Topology.Homology
