import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-! Gluing chartwise smooth representatives into a global tangent field. -/

open scoped Manifold ContDiff Topology _root_.Topology
open Function Set

noncomputable section

namespace HolomorphicAnosov

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
/-- Chartwise smooth tangent representatives that agree by the curve chain rule assemble into a globally smooth tangent field. (Bochner–Montgomery, Lemma 5.) -/
theorem chart_gluing_generator_g1
    (X : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hlocal : ∀ x, ∃ U ∈ 𝓝 x, CMDiff[U] ∞ (T% X)) :
    CMDiff ∞ (T% X) := by
  intro x
  rcases hlocal x with ⟨U, hU, hUX⟩
  exact hUX.contMDiffAt hU

end HolomorphicAnosov

