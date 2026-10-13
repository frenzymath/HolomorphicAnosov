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

/-- The two-point sphere base has finite discrete native topology.
Its coordinate equation is proved in the L² norm, not by identifying L² with
sup norm. Source: Hatcher Propositions 2.6 and 2.8, pp.109–110. -/
theorem zeroSphere_finite :
    Finite {x : EuclideanSpace ℝ (Fin 1) // ‖x‖ = 1} := by
  let ev : {x : EuclideanSpace ℝ (Fin 1) // ‖x‖ = 1} → ℝ := fun x ↦ x.val 0
  have hinj : Function.Injective ev := by
    intro x y h
    apply Subtype.ext
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi] using h
  have hr : (Set.range ev).Finite := by
    apply (Set.toFinite ({1, -1} : Set ℝ)).subset
    rintro t ⟨x, rfl⟩
    have hx : (x.val 0) ^ 2 = 1 := by
      have hn := EuclideanSpace.real_norm_sq_eq x.val
      simpa [x.property] using hn.symm
    have hc : x.val 0 = 1 ∨ x.val 0 = -1 := by
      have hp : (x.val 0 - 1) * (x.val 0 + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hp with h | h
      · left; linarith
      · right; linarith
    simpa [ev] using hc
  exact (Set.finite_range_iff hinj).mp hr

end HolomorphicAnosov.Topology.Homology
