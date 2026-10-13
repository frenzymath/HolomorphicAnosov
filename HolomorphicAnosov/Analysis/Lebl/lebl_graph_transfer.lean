import HolomorphicAnosov.Analysis.Complex.LeblPolydiscCoordinateDerivatives
import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.Connected.Basic
import HolomorphicAnosov.Analysis.Lebl.leblCoordinatePolydisc
import HolomorphicAnosov.Analysis.Lebl.leblUnpermuteGraphCoordinates
import HolomorphicAnosov.Analysis.Lebl.leblHolomorphicZeroSetGraphAt
import HolomorphicAnosov.Analysis.Lebl.isOpen_leblCoordinatePolydisc
import HolomorphicAnosov.Analysis.Lebl.lebl_unpermute_linear
import HolomorphicAnosov.Analysis.Lebl.lebl_unpermute_point
import HolomorphicAnosov.Analysis.Lebl.lebl_disk_zero_persistence

namespace HolomorphicAnosov.Analysis

open Set
open scoped ContDiff

/-- Lebl, Tasty Bits of Several Complex Variables v3.4, §1.6 Theorem 1.6.2 p.36.
Public auxiliary result in the regular-hypersurface proof. -/
lemma lebl_graph_transfer {n : ℕ}
    {U : Set (Fin (n + 1) → ℂ)} {a h : (Fin (n + 1) → ℂ) → ℂ}
    (hU : IsOpen U) (ha : DifferentiableOn ℂ a U)
    (hzero : ∀ z ∈ U, a z = 0 → h z = 0)
    {p : Fin (n + 1) → ℂ} (hap : a p = 0)
    (hpgraph : leblHolomorphicZeroSetGraphAt U h p) :
    leblHolomorphicZeroSetGraphAt U a p := by
  classical
  obtain ⟨hp, σ, c, r, d, s, g, hr, hs, hpy, hpw, hg, hmaps, hdom, heq⟩ := hpgraph
  obtain ⟨l, hl⟩ := lebl_unpermute_linear σ
  let y₀ : Fin n → ℂ := fun i ↦ p (σ i.castSucc)
  let w₀ : ℂ := p (σ (Fin.last n))
  let V := leblCoordinatePolydisc c r
  have hV : IsOpen V := isOpen_leblCoordinatePolydisc c r
  have hy₀ : y₀ ∈ V := hpy
  have hw₀ : w₀ ∈ Metric.ball d s := by simpa only [Metric.mem_ball, dist_eq_norm] using hpw
  have hlp : l (y₀, w₀) = p := by
    rw [hl]; exact lebl_unpermute_point σ p
  have hgw : g y₀ = w₀ := by
    apply Eq.symm
    exact (heq y₀ hy₀ w₀ hw₀).mp (by rw [← hl (y₀, w₀), hlp]; exact hp.2)
  let A : (Fin n → ℂ) × ℂ → ℂ := a ∘ l
  have hAd : DifferentiableOn ℂ A (l ⁻¹' U) :=
    ha.comp l.differentiable.differentiableOn (fun _ hz ↦ hz)
  have hO : IsOpen (l ⁻¹' U) := hU.preimage l.continuous
  have hAU : ∀ y ∈ V, ∀ w ∈ Metric.ball d s, (y, w) ∈ l ⁻¹' U := by
    intro y hy w hw
    rw [mem_preimage, hl]
    exact hdom y hy w hw
  have hAc : A (y₀, w₀) = 0 := by simp only [A, Function.comp_apply, hlp, hap]
  have hAnz : ∀ w ∈ Metric.ball d s, w ≠ w₀ → A (y₀, w) ≠ 0 := by
    intro w hw hne haz
    apply hne
    rw [← hgw]
    apply (heq y₀ hy₀ w hw).mp
    apply hzero _ (hdom y₀ hy₀ w hw)
    simpa only [A, Function.comp_apply, hl] using haz
  obtain ⟨R, hR, hRB⟩ := Metric.mem_nhds_iff.mp (Metric.isOpen_ball.mem_nhds hw₀)
  let R₀ := R / 2
  have hR₀ : 0 < R₀ := half_pos hR
  have hKD : Metric.closedBall w₀ R₀ ⊆ Metric.ball d s := by
    intro w hw
    apply hRB
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hw) (by dsimp [R₀]; linarith)
  have hslice : ∀ y ∈ V, AnalyticOnNhd ℂ (fun w ↦ A (y, w))
      (Metric.closedBall w₀ R₀) := by
    intro y hy
    have hd : DifferentiableOn ℂ (fun w ↦ A (y, w)) (Metric.ball d s) := by
      apply hAd.comp ((differentiable_const y).prodMk differentiable_id).differentiableOn
      exact fun w hw ↦ hAU y hy w hw
    exact (hd.analyticOnNhd Metric.isOpen_ball).mono hKD
  have hboundary : ∀ w ∈ Metric.sphere w₀ R₀, A (y₀, w) ≠ 0 := by
    intro w hw
    apply hAnz w (hKD (Metric.sphere_subset_closedBall hw))
    intro he
    subst w
    have := Metric.mem_sphere.mp hw
    simp only [dist_self] at this
    exact (ne_of_gt hR₀) this.symm
  have hnear : ∀ᶠ y in nhds y₀, ∀ w ∈ Metric.sphere w₀ R₀,
      ‖A (y, w) - A (y₀, w)‖ < ‖A (y₀, w)‖ := by
    apply (isCompact_sphere w₀ R₀).eventually_forall_of_forall_eventually
    intro w hw
    have hwD := hKD (Metric.sphere_subset_closedBall hw)
    have hAcont := (hAd.continuousOn.continuousAt (hO.mem_nhds (hAU y₀ hy₀ w hwD)))
    have hbase' : ContinuousAt (fun z : (Fin n → ℂ) × ℂ ↦ A (y₀, z.2)) (y₀, w) := by
      have hd : DifferentiableOn ℂ (fun v ↦ A (y₀, v)) (Metric.ball d s) :=
        hAd.comp ((differentiable_const y₀).prodMk differentiable_id).differentiableOn
          (fun v hv ↦ hAU y₀ hy₀ v hv)
      have hc : ContinuousAt (fun v : ℂ ↦ A (y₀, v)) w :=
        hd.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hwD)
      exact ContinuousAt.comp (g := fun v : ℂ ↦ A (y₀, v))
        (f := fun z : (Fin n → ℂ) × ℂ ↦ z.2) hc continuousAt_snd
    exact ((hAcont.sub hbase').norm.eventually_lt hbase'.norm
      (by simp [norm_pos_iff, hboundary w hw]))
  have hboth := Filter.inter_mem (hV.mem_nhds hy₀) hnear
  obtain ⟨δ, hδ, hδboth⟩ := Metric.mem_nhds_iff.mp hboth
  have hnew : ∀ y ∈ Metric.ball y₀ δ, A (y, g y) = 0 ∧
      g y ∈ Metric.ball w₀ R₀ := by
    intro y hy
    have hyV := (hδboth hy).1
    obtain ⟨w, hw, haw⟩ := lebl_disk_zero_persistence hR₀
      (hslice y₀ hy₀) (hslice y hyV) hAc hboundary (hδboth hy).2
    have hwD := hKD (Metric.ball_subset_closedBall hw)
    have hhw : h (leblUnpermuteGraphCoordinates σ y w) = 0 :=
      hzero _ (hdom y hyV w hwD) (by simpa only [A, Function.comp_apply, hl] using haw)
    have he : w = g y := (heq y hyV w hwD).mp hhw
    exact ⟨by simpa only [he] using haw, he ▸ hw⟩
  have hpoly : leblCoordinatePolydisc y₀ (fun _ ↦ δ) = Metric.ball y₀ δ := by
    ext y
    simp only [leblCoordinatePolydisc, mem_ofPred_eq, Metric.mem_ball, dist_eq_norm]
    exact (pi_norm_lt_iff hδ).symm
  refine ⟨⟨hp.1, hap⟩, σ, y₀, (fun _ ↦ δ), w₀, R₀, g,
    (fun _ ↦ hδ), hR₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpoly]; exact Metric.mem_ball_self hδ
  · simp only [w₀, sub_self, norm_zero]; exact hR₀
  · exact hg.mono (by rw [hpoly]; exact fun y hy ↦ (hδboth hy).1)
  · intro y hy; exact (hnew y (hpoly ▸ hy)).2
  · intro y hy w hw
    exact hdom y (hδboth (hpoly ▸ hy)).1 w
      (hKD (Metric.ball_subset_closedBall hw))
  · intro y hy w hw
    constructor
    · intro haz
      apply (heq y (hδboth (hpoly ▸ hy)).1 w
        (hKD (Metric.ball_subset_closedBall hw))).mp
      exact hzero _ (hdom y (hδboth (hpoly ▸ hy)).1 w
        (hKD (Metric.ball_subset_closedBall hw))) haz
    · intro he
      subst w
      simpa only [A, Function.comp_apply, hl] using (hnew y (hpoly ▸ hy)).1

end HolomorphicAnosov.Analysis
