import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open IsManifold TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov
noncomputable section

/-- The differential of an open inclusion is injective on each tangent fibre. -/
theorem smooth_open_inclusion_mfderiv_injective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (U : Opens M) (p : U) :
    Function.Injective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun q : U ↦ (q : M)) p) := by
  let e := U.openPartialHomeomorphSubtypeCoe ⟨p⟩
  have he : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) := by
    constructor
    · intro q _
      exact (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := ∞) q)
        |>.mdifferentiableAt (by simp) |>.mdifferentiableWithinAt
    · intro q hq
      have htarget : e.target ∈ 𝓝 q := e.open_target.mem_nhds hq
      have hid : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
          (Subtype.val ∘ e.symm) q :=
        contMDiffAt_id.congr_of_eventuallyEq
          (Filter.eventuallyEq_of_mem htarget fun z hz ↦ e.right_inv hz)
      exact ((ContMDiffAt.subtypeVal_comp_iff U e.symm q).mp hid).mdifferentiableAt
        (by simp) |>.mdifferentiableWithinAt
  exact he.mfderiv_injective (by simp [e])

end
end HolomorphicAnosov
