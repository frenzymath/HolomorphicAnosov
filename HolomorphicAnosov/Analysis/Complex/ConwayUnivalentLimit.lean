import HolomorphicAnosov.Analysis.Complex.ConwayZeroPersists
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Metrizable.Uniformity

namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- A nonconstant compact-uniform limit of holomorphic injections on a connected
open complex domain is injective.

Source: Conway VII Lemma 4.3, p.163; McMullen, Advanced Complex Analysis, Lemma 4.2,
pp.58–59. If f(x)=f(y) with x≠y, isolate the zero y of f−f(x) in a closed disk
excluding x. The identity theorem rules out an identically zero germ because f is
nonconstant. Its boundary has a positive minimum modulus. Compact-uniform convergence
of F_n and convergence at x make F_n−F_n(x) uniformly closer than this minimum on
the boundary. Zero persistence supplies a zero inside, contradicting injectivity of
F_n and the fact that x lies outside the disk. -/
theorem conway_univalent_limit
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hhol : ∀ n, DifferentiableOn ℂ (F n) U)
    (hinj : ∀ n, InjOn (F n) U)
    (hlim : ∀ K : Set ℂ, K ⊆ U → IsCompact K → TendstoUniformlyOn F f atTop K)
    (hnonconst : ¬∃ c : ℂ, EqOn f (fun _ ↦ c) U) : InjOn f U := by
  have hloc : TendstoLocallyUniformlyOn F f atTop U :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mpr hlim
  have hf : DifferentiableOn ℂ f U := hloc.differentiableOn (Eventually.of_forall hhol) hU
  have hfa := hf.analyticOnNhd hU
  intro x hx y hy heq
  by_contra hxy
  let q : ℂ → ℂ := fun z ↦ f z - f x
  have hqa : AnalyticOnNhd ℂ q U := hfa.sub analyticOnNhd_const
  have hqne : ∀ᶠ z in 𝓝[≠] y, q z ≠ 0 := by
    rcases (hqa y hy).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · have hz := hqa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hy hzero
      exact (hnonconst ⟨f x, fun z hzU ↦ sub_eq_zero.mp (hz hzU)⟩).elim
    · exact hne
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhdsWithin_iff.mp hqne
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hU y hy
  obtain ⟨r, hr, hrmin⟩ := exists_between
    (lt_min hε (lt_min hδ (dist_pos.mpr hxy)))
  have hrε := lt_of_lt_of_le hrmin (min_le_left _ _)
  have hrδ := lt_of_lt_of_le hrmin ((min_le_right _ _).trans (min_le_left _ _))
  have hrxy := lt_of_lt_of_le hrmin ((min_le_right _ _).trans (min_le_right _ _))
  have hKU : Metric.closedBall y r ⊆ U := fun z hz ↦ hδsub
    ((Metric.mem_closedBall.mp hz).trans_lt hrδ)
  have hbne : ∀ z ∈ Metric.sphere y r, q z ≠ 0 := by
    intro z hz
    apply hεsub
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Metric.mem_sphere.mp hz]
      exact hrε
    · show z ≠ y
      intro he
      have := Metric.mem_sphere.mp hz
      simp [he] at this
      linarith
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere y r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le)
    ((hqa.continuousOn.mono (Metric.sphere_subset_closedBall.trans hKU)).norm)
  let m := ‖q z₀‖
  have hm : 0 < m := norm_pos_iff.mpr (hbne z₀ hz₀)
  have hK : IsCompact (Metric.closedBall y r ∪ {x}) :=
    (isCompact_closedBall y r).union (isCompact_singleton)
  have hKsub : Metric.closedBall y r ∪ {x} ⊆ U := by
    intro z hz
    rcases hz with hz | hz
    · exact hKU hz
    · simpa only [mem_singleton_iff.mp hz] using hx
  obtain ⟨n, hn⟩ := ((Metric.tendstoUniformlyOn_iff.mp (hlim _ hKsub hK))
    (m / 3) (by positivity)).exists
  have hFn : AnalyticOnNhd ℂ (fun z ↦ F n z - F n x) (Metric.closedBall y r) :=
    ((hhol n).analyticOnNhd hU).sub analyticOnNhd_const |>.mono hKU
  obtain ⟨z, hz, hzero⟩ := conway_zero_persists_of_boundary_close y r hr q
    (fun z ↦ F n z - F n x) (hqa.mono hKU) hFn (by dsimp [q]; exact sub_eq_zero.mpr heq.symm) (by
      intro z hz
      have hze : ‖F n z - f z‖ < m / 3 := by
        simpa only [dist_eq_norm, norm_sub_rev] using hn z (Or.inl (Metric.sphere_subset_closedBall hz))
      have hxe : ‖F n x - f x‖ < m / 3 := by
        simpa only [dist_eq_norm, norm_sub_rev] using hn x (Or.inr (mem_singleton x))
      have htri : ‖(F n z - F n x) - q z‖ ≤ ‖F n z - f z‖ + ‖F n x - f x‖ := by
        have hid : (F n z - F n x) - q z = (F n z - f z) - (F n x - f x) := by dsimp [q]; abel
        rw [hid]
        exact norm_sub_le _ _
      have hmb : m ≤ ‖q z‖ := hmin hz
      linarith)
  have hzx : z = x := hinj n (hKU (Metric.ball_subset_closedBall hz)) hx (sub_eq_zero.mp hzero)
  have := Metric.mem_ball.mp hz
  rw [hzx] at this
  exact (not_lt_of_ge hrxy.le) this

end HolomorphicAnosov
