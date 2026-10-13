import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphChartCoordinateContinuity

noncomputable section
open Set _root_.Topology

namespace HolomorphicAnosov

/-!
HPS Theorem 5.5, pp. 8, 35 and 61--62: in genuine finite-rank bundle charts, a continuous
total fibre map has continuous operator-norm fields in the original fibre norms.  The proof
uses chart evaluation continuity, finite-dimensional continuous-linear-map extensionality, and
the compact model-sphere ratio formula.  This is isolated as a named Stage 2 proposition because
the current public atlas API does not yet expose the chart-coordinate continuity bridge.
-/
theorem parameter_graph_coordinate_norm_continuity
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
    Continuous (fun p ↦ ‖(T₁ p).symm.toContinuousLinearMap‖) ∧
    Continuous (fun p ↦ ‖T₂ p‖) := by
  obtain ⟨α, β, hα, hβ, hαeq, hβeq⟩ :=
    parameter_graph_chart_coordinate_continuity e h T₁ T₂ hT
  exact ⟨hαeq ▸ hα, hβeq ▸ hβ⟩

end HolomorphicAnosov
