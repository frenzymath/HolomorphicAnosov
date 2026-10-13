import HolomorphicAnosov.Geometry.Riemannian.SmoothPathEndpointFlattening

/-! Smooth paths with matching endpoints admit smooth concatenations with additive Riemannian
length. -/

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Bundle ENNReal Topology _root_.Topology

namespace HolomorphicAnosov

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Two smooth paths on `[0, 1]` with matching endpoints admit a smooth concatenation on `[0, 1]`
whose length is the sum of their lengths. -/
theorem exists_smooth_path_length_eq_add
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {c d : ℝ → M} (hc : ContMDiffOn 𝓘(ℝ) I ∞ c (Icc 0 1))
    (hd : ContMDiffOn 𝓘(ℝ) I ∞ d (Icc 0 1)) (hcd : c 1 = d 0) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ σ : ℝ → M, ContMDiff 𝓘(ℝ) I ∞ σ ∧ σ 0 = c 0 ∧ σ 1 = d 1 ∧
      Manifold.pathELength I σ 0 1 =
        Manifold.pathELength I c 0 1 + Manifold.pathELength I d 0 1 := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨c', hc', hc'0, hc'1, hclen, _, hcflat⟩ := smooth_path_endpoint_flattening g hc
  obtain ⟨d', hd', hd'0, hd'1, hdlen, hdflat, _⟩ := smooth_path_endpoint_flattening g hd
  let d'' : ℝ → M := fun t ↦ d' (t - 1)
  have hsub : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ ↦ t - 1) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hd'' : ContMDiff 𝓘(ℝ) I ∞ d'' := hd'.comp hsub
  have hdflat' : d'' =ᶠ[𝓝 1] (fun _ ↦ c 1) := by
    have hlim : Tendsto (fun t : ℝ ↦ t - 1) (𝓝 1) (𝓝 0) := by
      have heq : (fun t : ℝ ↦ t - 1) = id - fun _ : ℝ ↦ (1 : ℝ) := by
        funext t
        simp
      rw [heq]
      convert (continuous_id.sub
        (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℝ)))).tendsto 1 using 1 ;
        simp
    simpa only [Function.comp_def, hcd] using hdflat.comp_tendsto hlim
  let γ := piecewise (Iic 1) c' d''
  have hγ : ContMDiff 𝓘(ℝ) I ∞ γ :=
    hc'.piecewise_Iic hd'' (hcflat.trans hdflat'.symm)
  have hγ0 : γ 0 = c 0 := by simp [γ, hc'0]
  have hγ2 : γ 2 = d 1 := by norm_num [γ, d'', hd'1]
  have hγlen : Manifold.pathELength I γ 0 2 =
      Manifold.pathELength I c 0 1 + Manifold.pathELength I d 0 1 := by
    rw [← Manifold.pathELength_add zero_le_one one_le_two]
    congr 1
    · calc
        Manifold.pathELength I γ 0 1 = Manifold.pathELength I c' 0 1 := by
          apply Manifold.pathELength_congr
          intro t ht
          simp [γ, ht.2]
        _ = _ := hclen
    · calc
        Manifold.pathELength I γ 1 2 = Manifold.pathELength I d'' 1 2 := by
          apply Manifold.pathELength_congr_Ioo
          intro t ht
          simp [γ, ht.1]
        _ = Manifold.pathELength I d' 0 1 := by
          have h := Manifold.pathELength_comp_of_monotoneOn (I := I) (γ := d')
            one_le_two (f := fun t : ℝ ↦ t - 1)
            (by intro t ht u hu htu; linarith)
            ((contMDiff_iff_contDiff.mp hsub).differentiable (by simp)).differentiableOn
            (hd'.mdifferentiable (by simp)).mdifferentiableOn
          convert h using 1 <;> simp [d'', Function.comp_def] ; norm_num
        _ = _ := hdlen
  let η : ℝ → ℝ := fun t ↦ 2 * t
  have hη : ContDiff ℝ ∞ η := by dsimp [η]; fun_prop
  refine ⟨γ ∘ η, hγ.comp (contMDiff_iff_contDiff.mpr hη), ?_, ?_, ?_⟩
  · simpa [η] using hγ0
  · simpa [η] using hγ2
  · calc
      Manifold.pathELength I (γ ∘ η) 0 1 = Manifold.pathELength I γ 0 2 := by
        have h := Manifold.pathELength_comp_of_monotoneOn (I := I) (γ := γ)
          zero_le_one (f := η) (by intro t ht u hu htu; dsimp [η]; linarith)
          (hη.differentiable (by simp)).differentiableOn
          (hγ.mdifferentiable (by simp)).mdifferentiableOn
        simpa [η] using h
      _ = _ := hγlen

end HolomorphicAnosov

