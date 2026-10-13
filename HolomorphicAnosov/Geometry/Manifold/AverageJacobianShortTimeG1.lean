import Mathlib.Topology.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! Local persistence of invertibility for continuous operator families. (Bochner–Montgomery, Lemma 2.) -/

noncomputable section

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]
variable {α : Type v} [TopologicalSpace α]

/-- Invertibility persists locally for a continuous operator family based at an identity map. -/
theorem eventually_average_jacobian_invertible_g1
    (J : α → E →L[ℝ] E) (x₀ : α)
    (hJ : Continuous J) (h₀ : J x₀ = ContinuousLinearMap.id ℝ E) :
    ∀ᶠ x in 𝓝 x₀, (J x).IsInvertible := by
  have hId : (ContinuousLinearMap.id ℝ E).IsInvertible := by
    simpa only [ContinuousLinearEquiv.coe_refl] using
      (ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ E))
  have hOpen : ∀ᶠ T in 𝓝 (ContinuousLinearMap.id ℝ E), T.IsInvertible :=
    hId.eventually_nhds
  have hT : Filter.Tendsto J (𝓝 x₀) (𝓝 (ContinuousLinearMap.id ℝ E)) := by
    have hT0 := hJ.continuousAt (x := x₀)
    change Filter.Tendsto J (𝓝 x₀) (𝓝 (J x₀)) at hT0
    rw [h₀] at hT0
    exact hT0
  exact hT.eventually hOpen

end HolomorphicAnosov

