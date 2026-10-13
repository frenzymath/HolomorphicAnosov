import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Analysis.FrameOperatorNormContinuity
import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankAtlasFrameContinuity
import Mathlib.Topology.UniformSpace.UniformApproximation

noncomputable section
open Set Filter _root_.Topology
namespace HolomorphicAnosov

/-- Weighted uniform convergence in the original fibre norms preserves total-space continuity in a finite-rank normed atlas (HPS, pp.8, 35, 54–55, 62). -/
theorem parameter_graph_weighted_limit_continuity
    {X A : Type*} [TopologicalSpace X] [TopologicalSpace A]
    {E : A → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [TopologicalSpace (Sigma E)]
    (e : FiniteRankNormedAtlas (E := E))
    (b : X → A) (hb : Continuous b)
    (f : ℕ → ∀ x, E (b x)) (g : ∀ x, E (b x))
    (hf : ∀ n, Continuous (fun x ↦ (⟨b x, f n x⟩ : Sigma E)))
    (w : X → ℝ) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hc : Tendsto c atTop (𝓝 0))
    (hbound : ∀ n x, ‖f n x - g x‖ ≤ c n * w x) :
    Continuous (fun x ↦ (⟨b x, g x⟩ : Sigma E)) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro x₀
  let i := b x₀
  let U := (e.chart i).baseSet
  let frame (p : U) := (e.coordinates i p.1 p.2).symm
  have hden : Continuous (fun z : U × FiniteFiberModel (e.rank i) ↦
      ‖frame z.1 z.2‖) := e.continuous_norm.comp (atlas_frame_continuous e i)
  have hnum : Continuous (fun z : U × FiniteFiberModel (e.rank i) ↦
      ‖(e.coordinates i z.1.1 z.1.2) (frame z.1 z.2)‖) := by
    simpa only [frame, ContinuousLinearEquiv.apply_symm_apply] using
      (continuous_snd.norm : Continuous (fun z : U × FiniteFiberModel (e.rank i) ↦ ‖z.2‖))
  have hcoordnorm := continuous_norm_of_frame frame
    (fun p : U ↦ (e.coordinates i p.1 p.2).toContinuousLinearMap) hden hnum
  let N (p : A) : ℝ := if hp : p ∈ U then
    ‖(e.coordinates i p hp).toContinuousLinearMap‖ else 0
  have hNon : ContinuousOn N U := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply hcoordnorm.congr
    intro p
    simp only [Set.domRestrict, N, dite_eq_left p.2]
  have hi : i ∈ U := e.mem_baseSet i
  have hNat : ContinuousAt N i := hNon.continuousAt ((e.chart i).open_baseSet.mem_nhds hi)
  let K : ℝ := N i + 1
  let M : ℝ := w x₀ + 1
  have hK : 0 ≤ K := by
    have : 0 ≤ N i := by simp only [N, dite_eq_left hi]; exact norm_nonneg _
    dsimp [K]
    linarith
  have hM : 0 ≤ M := by dsimp [M]; linarith [hw0 x₀]
  let W : Set X := {x | b x ∈ U ∧ N (b x) < K ∧ w x < M}
  have hW : W ∈ 𝓝 x₀ := by
    have hu : ∀ᶠ x in 𝓝 x₀, b x ∈ U :=
      hb.continuousAt.preimage_mem_nhds ((e.chart i).open_baseSet.mem_nhds hi)
    have hn : ∀ᶠ x in 𝓝 x₀, N (b x) < K :=
      (hNat.comp hb.continuousAt).eventually_lt_const (by dsimp [K, i]; linarith)
    have hm : ∀ᶠ x in 𝓝 x₀, w x < M :=
      hw.continuousAt.eventually_lt_const (by dsimp [M]; linarith)
    exact hu.and (hn.and hm)
  let u (n : ℕ) (x : X) := ((e.chart i) ⟨b x, f n x⟩).2
  let v (x : X) := ((e.chart i) ⟨b x, g x⟩).2
  have herr (n : ℕ) (x : X) (hx : x ∈ W) :
      dist (u n x) (v x) ≤ K * (c n * M) := by
    have hnorm : ‖(e.coordinates i (b x) hx.1).toContinuousLinearMap‖ ≤ K := by
      have := hx.2.1.le
      simpa only [N, dite_eq_left hx.1] using this
    change dist (((e.chart i) ⟨b x, f n x⟩).2)
      (((e.chart i) ⟨b x, g x⟩).2) ≤ _
    rw [e.chart_apply i (b x) hx.1, e.chart_apply i (b x) hx.1]
    simp only [dist_eq_norm, ← map_sub]
    calc
      _ ≤ ‖(e.coordinates i (b x) hx.1).toContinuousLinearMap‖ * ‖f n x - g x‖ :=
        (e.coordinates i (b x) hx.1).toContinuousLinearMap.le_opNorm _
      _ ≤ K * (c n * w x) := mul_le_mul hnorm (hbound n x) (norm_nonneg _) hK
      _ ≤ K * (c n * M) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hx.2.2.le (hc0 n)) hK
  have hlim : TendstoUniformlyOn u v atTop W := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have htail : Tendsto (fun n ↦ K * (c n * M)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul (hc.mul_const M))
    filter_upwards [htail.eventually_lt_const hε] with n hn x hx
    rw [dist_comm]
    exact (herr n x hx).trans_lt hn
  have hvc : ContinuousOn v W := hlim.continuousOn
    (Eventually.of_forall (fun n ↦
      ((e.chart i).toOpenPartialHomeomorph.continuousOn.comp (hf n).continuousOn
        (fun x hx ↦ (e.chart i).mem_source.mpr hx.1)).snd)).frequently
  apply (e.chart i).continuousAt_of_comp_left
    (show ContinuousAt (fun x ↦ (⟨b x, g x⟩ : Sigma E).1) x₀ from hb.continuousAt) hi
  have hpair : ContinuousAt (fun x ↦ (b x, v x)) x₀ :=
    hb.continuousAt.prodMk (hvc.continuousAt hW)
  apply hpair.congr_of_eventuallyEq
  filter_upwards [hW] with x hx
  exact ((e.chart i).mk_proj_snd' (x := (⟨b x, g x⟩ : Sigma E)) hx.1).symm

end HolomorphicAnosov
