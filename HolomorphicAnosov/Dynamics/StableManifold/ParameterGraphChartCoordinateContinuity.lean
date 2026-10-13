import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphTotalMapContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphChartLocalOperatorNormContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphChartLocalOperatorNormContinuity

noncomputable section
open Set _root_.Topology

namespace HolomorphicAnosov

/-!
HPS pp. 8, 35 and 61--62, chart-coordinate bridge: after restricting to a genuine finite-rank
bundle chart, the continuous total fibre map is represented by a continuous family of finite
dimensional operators.  The operator inverse on the first block and the second block therefore
have continuous original operator norms.  This named Stage 2 proposition isolates the precise
chart/API obligation used by the norm-continuity provider; the present atlas structure does not
yet expose its proof as a public declaration.
-/
theorem parameter_graph_chart_coordinate_continuity
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {E₁ E₂ : A → Type*}
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    [TopologicalSpace (Sigma E₁)] [TopologicalSpace (Sigma E₂)]
    [TopologicalSpace (Sigma (fun p ↦ E₁ p × E₂ p))]
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂)) (h : A ≃ₜ A)
    (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p))
    (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (hT : Continuous (fun z : Sigma (fun p ↦ E₁ p × E₂ p) ↦
      (⟨h z.1, (T₁ z.1 z.2.1, T₂ z.1 z.2.2)⟩ :
        Sigma (fun p ↦ E₁ p × E₂ p)))) :
    ∃ α β : A → ℝ,
      Continuous α ∧ Continuous β ∧
      α = (fun p ↦ ‖(T₁ p).symm.toContinuousLinearMap‖) ∧
      β = (fun p ↦ ‖T₂ p‖) := by
  have hloc := parameter_graph_chart_local_operator_norm_continuity (e := e) h T₁ T₂ hT
  let α : A → ℝ := fun p ↦ ‖(T₁ p).symm.toContinuousLinearMap‖
  let β : A → ℝ := fun p ↦ ‖T₂ p‖
  have hα : Continuous α := continuous_iff_continuousAt.2 (fun p ↦ (hloc p).1)
  have hβ : Continuous β := continuous_iff_continuousAt.2 (fun p ↦ (hloc p).2)
  exact ⟨α, β, hα, hβ, rfl, rfl⟩

end HolomorphicAnosov
