import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ZeroSphere_discrete

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- The native one-dimensional Euclidean unit sphere has exactly the
negative and positive coordinate-unit points. Its topology is discrete. -/
def zeroSphereBoolHomeomorph :
    {x : EuclideanSpace ℝ (Fin 1) // ‖x‖ = 1} ≃ₜ Bool := by
  let S := {x : EuclideanSpace ℝ (Fin 1) // ‖x‖ = 1}
  letI : DiscreteTopology S := zeroSphere_discrete
  let f : Bool → S := fun b ↦
    ⟨PiLp.single 2 (0 : Fin 1) (if b then (1 : ℝ) else -1), by cases b <;> simp⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h := congrArg (fun x : S ↦ x.val 0) hab
      cases a <;> cases b
      · rfl
      · norm_num [f] at h
      · norm_num [f] at h
      · rfl
    · intro x
      have hx : (x.val 0) ^ 2 = 1 := by
        have hn := EuclideanSpace.real_norm_sq_eq x.val
        simpa [x.property] using hn.symm
      have hc : x.val 0 = 1 ∨ x.val 0 = -1 := by
        have hp : (x.val 0 - 1) * (x.val 0 + 1) = 0 := by nlinarith
        rcases mul_eq_zero.mp hp with h | h
        · left; linarith
        · right; linarith
      rcases hc with h | h
      · refine ⟨true, ?_⟩
        apply Subtype.ext
        ext i
        have hi : i = 0 := Subsingleton.elim _ _
        simp [f, hi, h]
      · refine ⟨false, ?_⟩
        apply Subtype.ext
        ext i
        have hi : i = 0 := Subsingleton.elim _ _
        simp [f, hi, h]
  exact (Homeomorph.ofDiscrete (Equiv.ofBijective f hf)).symm

end HolomorphicAnosov.Topology.Homology
