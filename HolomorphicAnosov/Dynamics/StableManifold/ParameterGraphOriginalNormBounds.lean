import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphOriginalNormBoundsInterface

noncomputable section
open Set _root_.Topology

namespace HolomorphicAnosov

/-! The compact varying-fibre norm step of HPS Theorem 5.5.

This is intentionally a named work item: the proof must build local chart
operator families, identify their compact-sphere suprema with the supplied
original operator norms, and then use compactness of the base. -/

/-- On a compact base, continuity of the total fibre map and genuine finite-rank
bundle charts make the original norms of the two diagonal blocks uniformly bounded.
The proof follows HPS pp. 8, 35 and 61--62: finite local chart covers, compact
model spheres, continuous ratio suprema, and `isLUB_csSup`. It treats zero-rank
fibres separately and does not replace the supplied fibre norms. -/
theorem parameter_graph_original_norm_bounds
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
    (∀ p, ‖(T₁ p).symm.toContinuousLinearMap‖ ≤
      sSup (Set.range (fun q ↦ ‖(T₁ q).symm.toContinuousLinearMap‖))) ∧
    (∀ p, ‖T₂ p‖ ≤ sSup (Set.range (fun q ↦ ‖T₂ q‖))) := by
  obtain ⟨hB₁, hB₂⟩ := parameter_graph_original_norm_bounds_interface e h T₁ T₂ hT
  exact ⟨fun p ↦ le_csSup hB₁ ⟨p, rfl⟩, fun p ↦ le_csSup hB₂ ⟨p, rfl⟩⟩

end HolomorphicAnosov
