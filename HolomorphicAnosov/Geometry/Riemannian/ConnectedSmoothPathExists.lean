import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.Connected.Clopen

open Set Filter
open scoped ContDiff Manifold Topology _root_.Topology

namespace HolomorphicAnosov

theorem connected_smooth_path_exists
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [PreconnectedSpace M] (x y : M) :
    ∃ c : ℝ → M, ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) ∞ c ∧ c 0 = x ∧ c 1 = y := by
  classical
  let R : M → M → Prop := fun a b ↦ ∃ c : ℝ → M,
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) ∞ c ∧ c 0 = a ∧ c 1 = b ∧
      c =ᶠ[𝓝 0] (fun _ ↦ a) ∧ c =ᶠ[𝓝 1] (fun _ ↦ b)
  let η : ℝ → ℝ := fun t ↦ Real.smoothTransition (3 * t - 1)
  have hη : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ η := by
    rw [contMDiff_iff_contDiff]
    dsimp [η]
    fun_prop
  have hη0 : η =ᶠ[𝓝 0] (fun _ ↦ 0) := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num)] with t ht
    change t < 1 / 3 at ht
    apply Real.smoothTransition.zero_iff_nonpos.mpr
    linarith
  have hη1 : η =ᶠ[𝓝 1] (fun _ ↦ 1) := by
    filter_upwards [Ioi_mem_nhds (show (2 / 3 : ℝ) < 1 by norm_num)] with t ht
    change 2 / 3 < t at ht
    apply Real.smoothTransition.eq_one_iff_one_le.mpr
    linarith
  have hηmem : MapsTo η univ (Icc 0 1) := fun t _ ↦
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hlocal (a : M) : ∀ᶠ b in 𝓝 a, R a b ∧ R b a := by
    let e := chartAt E a
    have ha : a ∈ e.source := mem_chart_source _ _
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target (e a) (e.map_source ha)
    have hn : e ⁻¹' Metric.ball (e a) ε ∩ e.source ∈ 𝓝 a :=
      inter_mem (e.continuousAt ha |>.preimage_mem_nhds (Metric.ball_mem_nhds _ hε))
        (e.open_source.mem_nhds ha)
    filter_upwards [hn] with b hb
    have hsegment (u v : M) (hu : u ∈ e.source) (hv : v ∈ e.source)
        (hu' : e u ∈ Metric.ball (e a) ε) (hv' : e v ∈ Metric.ball (e a) ε) : R u v := by
      let α : ℝ → M := e.symm ∘ AffineMap.lineMap (e u) (e v)
      have hα : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ α (Icc 0 1) := by
        apply contMDiffOn_chart_symm.comp
        · rw [contMDiffOn_iff_contDiffOn]
          exact (AffineMap.contDiff_lineMap _ _).contDiffOn
        · exact ((convex_ball (e a) ε).mapsTo_lineMap hu' hv').mono_right hball
      have h0 : α 0 = u := by simp [α, e.left_inv hu]
      have h1 : α 1 = v := by simp [α, e.left_inv hv]
      refine ⟨α ∘ η, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← contMDiffOn_univ]
        exact hα.comp hη.contMDiffOn hηmem
      · simpa [hη0.eq_of_nhds] using h0
      · simpa [hη1.eq_of_nhds] using h1
      · filter_upwards [hη0] with t ht
        simpa [ht] using h0
      · filter_upwards [hη1] with t ht
        simpa [ht] using h1
    exact ⟨hsegment a b ha hb.2 (Metric.mem_ball_self hε) hb.1,
      hsegment b a hb.2 ha hb.1 (Metric.mem_ball_self hε)⟩
  have htrans : IsTrans M R := by
    refine ⟨?_⟩
    intro a b d hab hbd
    rcases hab with ⟨c, hc, hc0, hc1, hcflat0, hcflat1⟩
    rcases hbd with ⟨e, he, he0, he1, heflat0, heflat1⟩
    let e' : ℝ → M := fun t ↦ e (t - 1)
    have hsub : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ ↦ t - 1) := by
      rw [contMDiff_iff_contDiff]
      fun_prop
    have he' : ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) ∞ e' := he.comp hsub
    have hlim : Tendsto (fun t : ℝ ↦ t - 1) (𝓝 1) (𝓝 0) := by
      convert (continuous_id.sub (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℝ)))).tendsto (1 : ℝ) using 1
      · ext t
        simp [Pi.sub_apply]
      · simp [Pi.sub_apply]
    have heflat' : e' =ᶠ[𝓝 1] (fun _ ↦ b) := heflat0.comp_tendsto hlim
    let γ := piecewise (Iic 1) c e'
    have hγ : ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) ∞ γ :=
      hc.piecewise_Iic he' (hcflat1.trans heflat'.symm)
    have hscale : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ ↦ 2 * t) := by
      rw [contMDiff_iff_contDiff]
      fun_prop
    refine ⟨fun t ↦ γ (2 * t), hγ.comp hscale, ?_, ?_, ?_, ?_⟩
    · simpa [γ] using hc0
    · norm_num [γ, e', he1]
    · have hl : Tendsto (fun t : ℝ ↦ 2 * t) (𝓝 0) (𝓝 0) := by
        convert ((continuous_const : Continuous (fun _ : ℝ ↦ (2 : ℝ))).mul continuous_id).tendsto (0 : ℝ) using 1
        · ext t
          simp [Pi.mul_apply]
        · simp [Pi.mul_apply]
      filter_upwards [hcflat0.comp_tendsto hl,
        Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)] with t ht ht'
      have hle : 2 * t ≤ (1 : ℝ) := by
        change t < 1 / 2 at ht'
        linarith
      simpa [γ, Set.piecewise, hle] using ht
    · have hl : Tendsto (fun t : ℝ ↦ 2 * t - 1) (𝓝 1) (𝓝 1) := by
        convert (((continuous_const : Continuous (fun _ : ℝ ↦ (2 : ℝ))).mul continuous_id).sub
          (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℝ)))).tendsto (1 : ℝ) using 1
        · ext t
          simp [Pi.sub_apply, Pi.mul_apply]
        · norm_num [Pi.sub_apply, Pi.mul_apply]
      filter_upwards [heflat1.comp_tendsto hl,
        Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)] with t ht ht'
      have hnle : ¬ 2 * t ≤ (1 : ℝ) := by
        change 1 / 2 < t at ht'
        linarith
      simpa [γ, e', Set.piecewise, hnle] using ht
  have hxy : R x y := PreconnectedSpace.induction₂' R hlocal htrans x y
  obtain ⟨c, hc, hc0, hc1, _, _⟩ := hxy
  exact ⟨c, hc, hc0, hc1⟩

end HolomorphicAnosov

