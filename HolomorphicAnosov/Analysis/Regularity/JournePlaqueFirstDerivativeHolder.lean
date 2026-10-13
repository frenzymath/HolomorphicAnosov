import HolomorphicAnosov.Analysis.Regularity.JourneGraphBoxPlaqueHasFDerivAt
import HolomorphicAnosov.Analysis.LowerJetHolderBound
import HolomorphicAnosov.Analysis.FDerivHolderBound

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

/-- A graph box with finite C^{n,α} bounds, n≥1, has a common α-Hölder constant for the first derivatives of all its framed plaques. -/
theorem graphBox_plaque_fderiv_holder_bound
    {d c N n : ℕ} {α : ℝ} {Ω : Set (Block N)}
    (b : GraphBox d c N n α Ω) (hn : 1 ≤ n)
    (hαpos : 0 < α) (hαle : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ Metric.ball 0 b.transverseRadius,
      ∀ x ∈ Metric.ball 0 b.leafRadius, ∀ y ∈ Metric.ball 0 b.leafRadius,
        ‖fderiv ℝ (b.plaque w) x - fderiv ℝ (b.plaque w) y‖ ≤ C * ‖x - y‖ ^ α := by
  obtain ⟨K, hK, hb⟩ := b.graph_bounds
  refine ⟨‖b.frame.toContinuousLinearMap‖ * (2 * K), by positivity, ?_⟩
  intro w hw x hx y hy
  have hfirst : ∀ x ∈ Metric.ball 0 b.leafRadius, ∀ y ∈ Metric.ball 0 b.leafRadius,
      ‖iteratedFDeriv ℝ 1 (b.graph w) x - iteratedFDeriv ℝ 1 (b.graph w) y‖ ≤
        (2 * K) * ‖x - y‖ ^ α := by
    intro x hx y hy
    by_cases h1 : n = 1
    · subst n
      exact ((hb w hw).2.2 x hx y hy).trans (by
        have hp := Real.rpow_nonneg (norm_nonneg (x - y)) α
        nlinarith)
    · have hh := lower_jet_holder_bound (Metric.ball 0 b.leafRadius)
        Metric.isOpen_ball (convex_ball _ _) n α K hαpos hαle hK (b.graph w) (hb w hw).1
        (fun k hk z hz ↦ by
          rw [iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hz]
          exact (hb w hw).2.1 k hk z hz) 1 (by omega) x hx y hy
      simpa only [iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hx,
        iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hy] using hh
  have hgraph : ‖fderiv ℝ (b.graph w) x - fderiv ℝ (b.graph w) y‖ ≤
      (2 * K) * ‖x - y‖ ^ α := by
    have hg1 : ContDiffOn ℝ 1 (b.graph w) (Metric.ball 0 b.leafRadius) :=
      (hb w hw).1.of_le (by exact_mod_cast hn)
    have hh := (fderiv_holder_bound (Metric.ball 0 b.leafRadius) Metric.isOpen_ball 0
      (b.graph w) hg1 (2 * K) α
      (fun k hk z hz ↦ ((hb w hw).2.1 k (hk.trans hn) z hz).trans (by linarith))
      hfirst).2.2 x hx y hy
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      ← map_sub, LinearIsometryEquiv.norm_map] using hh
  rw [(graphBox_plaque_hasFDerivAt b hn hw hx).fderiv,
    (graphBox_plaque_hasFDerivAt b hn hw hy).fderiv,
    ← ContinuousLinearMap.comp_sub]
  have hid : (ContinuousLinearMap.id ℝ (Block d)).prod (fderiv ℝ (b.graph w) x) -
      (ContinuousLinearMap.id ℝ (Block d)).prod (fderiv ℝ (b.graph w) y) =
      (0 : Block d →L[ℝ] Block d).prod
        (fderiv ℝ (b.graph w) x - fderiv ℝ (b.graph w) y) := by
    ext v <;> simp
  rw [hid]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  rw [ContinuousLinearMap.opNorm_prod]
  simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  calc
    _ ≤ ‖b.frame.toContinuousLinearMap‖ * ((2 * K) * ‖x - y‖ ^ α) :=
      mul_le_mul_of_nonneg_left hgraph (norm_nonneg _)
    _ = _ := by ring

/-- With at least two bounded spatial derivatives, the same framed plaque derivative fields are uniformly Lipschitz. -/
theorem graphBox_plaque_fderiv_lipschitz_bound
    {d c N n : ℕ} {α : ℝ} {Ω : Set (Block N)}
    (b : GraphBox d c N n α Ω) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ Metric.ball 0 b.transverseRadius,
      ∀ x ∈ Metric.ball 0 b.leafRadius, ∀ y ∈ Metric.ball 0 b.leafRadius,
        ‖fderiv ℝ (b.plaque w) x - fderiv ℝ (b.plaque w) y‖ ≤ C * ‖x - y‖ := by
  obtain ⟨K, hK, hb⟩ := b.graph_bounds
  refine ⟨‖b.frame.toContinuousLinearMap‖ * K, by positivity, ?_⟩
  intro w hw x hx y hy
  have hdiff : ∀ z ∈ Metric.ball 0 b.leafRadius,
      DifferentiableAt ℝ (fderiv ℝ (b.graph w)) z := by
    intro z hz
    have hf : ContDiffOn ℝ 1 (fderiv ℝ (b.graph w)) (Metric.ball 0 b.leafRadius) :=
      (hb w hw).1.fderiv_of_isOpen Metric.isOpen_ball (by exact_mod_cast hn)
    exact (hf.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by norm_num)
  have hnorm : ∀ z ∈ Metric.ball 0 b.leafRadius,
      ‖fderiv ℝ (fderiv ℝ (b.graph w)) z‖ ≤ K := by
    intro z hz
    rw [← norm_iteratedFDeriv_one (fderiv ℝ (b.graph w)), norm_iteratedFDeriv_fderiv]
    exact (hb w hw).2.1 2 hn z hz
  have hgraph := (convex_ball (0 : Block d) b.leafRadius).norm_image_sub_le_of_norm_fderiv_le
    hdiff hnorm hy hx
  rw [(graphBox_plaque_hasFDerivAt b (by omega) hw hx).fderiv,
    (graphBox_plaque_hasFDerivAt b (by omega) hw hy).fderiv,
    ← ContinuousLinearMap.comp_sub]
  have hid : (ContinuousLinearMap.id ℝ (Block d)).prod (fderiv ℝ (b.graph w) x) -
      (ContinuousLinearMap.id ℝ (Block d)).prod (fderiv ℝ (b.graph w) y) =
      (0 : Block d →L[ℝ] Block d).prod
        (fderiv ℝ (b.graph w) x - fderiv ℝ (b.graph w) y) := by
    ext v <;> simp
  rw [hid]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  rw [ContinuousLinearMap.opNorm_prod]
  simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  calc
    _ ≤ ‖b.frame.toContinuousLinearMap‖ * (K * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left hgraph (norm_nonneg _)
    _ = _ := by ring


end HolomorphicAnosov.JourneLeafPolynomialApproximation
