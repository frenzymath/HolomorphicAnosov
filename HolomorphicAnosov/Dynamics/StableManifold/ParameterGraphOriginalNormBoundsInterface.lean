import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphCoordinateNormContinuity

noncomputable section
open Set _root_.Topology

namespace HolomorphicAnosov

/-!
This is the reusable source/API interface for the compact varying-fibre norm step in HPS
Theorem 5.5 (pp. 8, 35 and 61--62). In local finite-rank bundle charts, continuity of the
total fibre map gives continuity of the coordinate operator families; compactness of the base
and of the finite-dimensional model spheres then gives bounded original operator-norm ranges.
The current atlas API does not expose the required chart-coordinate continuity lemma, so this
named proposition records that precise Stage 2 obligation rather than hiding it in the parent.
-/
theorem parameter_graph_original_norm_bounds_interface
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
    BddAbove (Set.range (fun q ↦ ‖(T₁ q).symm.toContinuousLinearMap‖)) ∧
    BddAbove (Set.range (fun q ↦ ‖T₂ q‖)) := by
  obtain ⟨hcont₁, hcont₂⟩ := parameter_graph_coordinate_norm_continuity e h T₁ T₂ hT
  constructor
  · have hi := isCompact_univ.bddAbove_image hcont₁.continuousOn
    have heq : (fun q ↦ ‖(T₁ q).symm.toContinuousLinearMap‖) '' Set.univ =
        Set.range (fun q ↦ ‖(T₁ q).symm.toContinuousLinearMap‖) := by
      ext x
      simp
    rw [← heq]
    exact hi
  · have hi := isCompact_univ.bddAbove_image hcont₂.continuousOn
    have heq : (fun q ↦ ‖T₂ q‖) '' Set.univ = Set.range (fun q ↦ ‖T₂ q‖) := by
      ext x
      simp
    rw [← heq]
    exact hi

end HolomorphicAnosov
