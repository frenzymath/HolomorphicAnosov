import HolomorphicAnosov.Geometry.SmoothAffineConnection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.Pullback
open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
namespace ConnectionChristoffelLocal
omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The derivative of an open inclusion identifies the tangent fibres of the restricted manifold. (Andrews, Prop. 8.3.1) -/
theorem inclusion_mfderiv_isInvertible {U V : Opens M} (hUV : U ≤ V) (p : U) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Opens.inclusion hUV) p).IsInvertible := by
  let : Nonempty U := ⟨p⟩
  let e : OpenPartialHomeomorph U V :=
    (Opens.isOpenEmbedding_of_le hUV).toOpenPartialHomeomorph (Opens.inclusion hUV)
  have heD : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) := by
    constructor
    · exact (contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) hUV).contMDiffOn.mdifferentiableOn (by simp)
    · intro q hq
      have hsame : (Subtype.val ∘ e.symm : V → M) =ᶠ[𝓝 q] (Subtype.val : V → M) := by
        filter_upwards [e.open_target.mem_nhds hq] with x hx
        exact congrArg Subtype.val (e.right_inv hx)
      have hsm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (Subtype.val ∘ e.symm : V → M) q :=
        (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := V) (n := ∞) q).congr_of_eventuallyEq hsame
      have hs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm q :=
        (ContMDiffAt.subtypeVal_comp_iff U e.symm q).mp hsm
      exact (hs.mdifferentiableAt (by simp)).mdifferentiableWithinAt
  exact ⟨heD.mfderiv (by simp [e]), rfl⟩

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
