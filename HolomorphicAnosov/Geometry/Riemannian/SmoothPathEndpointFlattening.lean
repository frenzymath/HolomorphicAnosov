import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-! Smooth paths admit reparametrizations that are constant near the endpoints and preserve
Riemannian length. -/

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Bundle ENNReal Topology _root_.Topology

namespace HolomorphicAnosov

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A smooth path on `[0, 1]` admits a globally smooth reparametrization that is constant near both
endpoints and has the same endpoints and Riemannian length. -/
theorem smooth_path_endpoint_flattening
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {c : ℝ → M} (hc : ContMDiffOn 𝓘(ℝ) I ∞ c (Icc 0 1)) :
    let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ σ : ℝ → M, ContMDiff 𝓘(ℝ) I ∞ σ ∧ σ 0 = c 0 ∧ σ 1 = c 1 ∧
      Manifold.pathELength I σ 0 1 = Manifold.pathELength I c 0 1 ∧
      σ =ᶠ[𝓝 0] (fun _ ↦ c 0) ∧ σ =ᶠ[𝓝 1] (fun _ ↦ c 1) := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨a, ha, ha1⟩ := exists_between (zero_lt_one : (0 : ℝ) < 1)
  obtain ⟨b, hab, hb⟩ := exists_between ha1
  let η (t : ℝ) : ℝ := Real.smoothTransition ((b - a)⁻¹ * (t - a))
  have hη0 (t : ℝ) (ht : t < a) : η t = 0 := by
    simp only [η, Real.smoothTransition.zero_iff_nonpos]
    apply mul_nonpos_of_nonneg_of_nonpos
    · simpa using hab.le
    · linarith
  have hη1 (t : ℝ) (ht : b < t) : η t = 1 := by
    simp only [η, Real.smoothTransition.eq_one_iff_one_le, inv_mul_eq_div]
    rw [one_le_div₀] <;> linarith
  have hηsmooth : ContDiff ℝ ∞ η := by dsimp [η]; fun_prop
  have hσ : ContMDiff 𝓘(ℝ) I ∞ (c ∘ η) := by
    rw [← contMDiffOn_univ]
    apply hc.comp
    · rw [contMDiffOn_univ, contMDiff_iff_contDiff]
      exact hηsmooth
    · intro t _
      exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  refine ⟨c ∘ η, hσ, by simp [hη0 0 ha], by simp [hη1 1 hb], ?_, ?_, ?_⟩
  · convert Manifold.pathELength_comp_of_monotoneOn (I := I) (γ := c)
      zero_le_one (f := η) ?_ (hηsmooth.differentiable (by simp)).differentiableOn
      ?_ using 1
    · rw [hη0 0 ha, hη1 1 hb]
    · apply Monotone.monotoneOn
      apply Real.smoothTransition.monotone.comp
      intro t u htu
      dsimp only
      gcongr
    · rw [hη0 0 ha, hη1 1 hb]
      exact hc.mdifferentiableOn (by simp)
  · filter_upwards [Iio_mem_nhds ha] with t ht
    simp [hη0 t ht]
  · filter_upwards [Ioi_mem_nhds hb] with t ht
    simp [hη1 t ht]

end HolomorphicAnosov

