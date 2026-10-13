import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open Set MeasureTheory Bundle
open scoped Manifold ContDiff Bundle ENNReal

namespace HolomorphicAnosov

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A C¹ path has finite Riemannian length on a compact interval. (Lee, p.275) -/
theorem c1_path_elength_ne_top
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {a b : ℝ} (hab : a ≤ b) {c : ℝ → M}
    (hc : ContMDiffOn 𝓘(ℝ) I 1 c (Icc a b)) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    Manifold.pathELength I c a b ≠ ⊤ := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  have ht := hc.continuousOn_tangentMapWithin (le_refl 1)
    (uniqueDiffOn_Icc hab).uniqueMDiffOn
  have hconst : Continuous (fun t : ℝ ↦
      (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hv : ContinuousOn (fun t ↦
      (⟨c t, mfderivWithin 𝓘(ℝ) I c (Icc a b) t 1⟩ : TangentBundle I M))
      (Icc a b) := ht.comp hconst.continuousOn (fun _ h ↦ h)
  have hs : ContinuousOn (fun t ↦ Real.sqrt (g.inner (c t)
      (mfderivWithin 𝓘(ℝ) I c (Icc a b) t 1)
      (mfderivWithin 𝓘(ℝ) I c (Icc a b) t 1))) (Icc a b) :=
    (hv.inner_bundle hv).sqrt
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hs
  apply ne_of_lt
  rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
  calc
    _ ≤ ∫⁻ _t in Icc a b, ENNReal.ofReal C := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      rw [← ofReal_norm, norm_eq_sqrt_real_inner]
      exact ENNReal.ofReal_le_ofReal (hC ⟨t, ht, rfl⟩)
    _ < ⊤ := by
      simp only [setLIntegral_const, Real.volume_Icc]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end HolomorphicAnosov

