import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

noncomputable section
open Filter _root_.Topology
namespace HolomorphicAnosov

/-- HPS, *Invariant Manifolds*, pp.54–58 and the parameter insertion on p.62:
a single perturbation threshold makes the image, preimage and first-jet graph
transforms contractions, while keeping the vertical cone rate below `ρ`.

The scalar coefficients are continuous at zero because both denominators equal
one there. Their limiting contraction coefficient is `a*k < 1`, while the
vertical coefficients limit to `k < ρ`. Each strict inequality therefore holds
on a neighborhood of zero. Intersect the finitely many neighborhoods and choose
a positive metric-ball radius. Nonnegative perturbations below that radius obey
all inequalities simultaneously. This proof retains zero horizontal rank (`a=0`)
and only introduces the reciprocal of `a` in the guarded nonzero-rank expansion clause. -/
theorem parameter_graph_contraction_threshold
    (a k ρ : ℝ) (ha0 : 0 ≤ a) (hk0 : 0 ≤ k) (hρ : 0 < ρ)
    (ha : a < ρ⁻¹) (hk : k < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ →
      2 * a * ε < 1 ∧
      0 < 1 - a * ε ∧ 0 < 1 - 2 * a * ε ∧
      a * (k + ε) / (1 - a * ε) ^ 2 < 1 ∧
      a * (k + ε) / (1 - 2 * a * ε) < 1 ∧
      a * (k + 2 * ε) / (1 - 2 * a * ε) < 1 ∧
      a * (k + 2 * ε) < 1 ∧
      (k + 2 * ε) * (a / (1 - a * ε)) < 1 ∧
      (k + ε) / (1 - a * ε) < ρ ∧ k + 2 * ε < ρ ∧
      a / (1 - a * ε) < ρ⁻¹ ∧
      (1 ≤ ρ → a / (1 - a * ε) < min 1 ρ⁻¹) ∧
      (ρ ≤ 1 → k + ε < min 1 ρ) ∧
      (0 < a → ρ < a⁻¹ - 3 * ε) := by
  have hak : a * k < 1 := by
    calc
      a * k < ρ⁻¹ * ρ := by gcongr
      _ = 1 := inv_mul_cancel₀ hρ.ne'
  have hlin : ContinuousAt (fun ε : ℝ ↦ 2 * a * ε) 0 := by fun_prop
  have hq₁ : ContinuousAt (fun ε : ℝ ↦ a * (k + ε) / (1 - a * ε) ^ 2) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
  have hq₂ : ContinuousAt (fun ε : ℝ ↦ a * (k + ε) / (1 - 2 * a * ε)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
  have hqJ : ContinuousAt (fun ε : ℝ ↦ a * (k + 2 * ε) / (1 - 2 * a * ε)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
  have hslope : ContinuousAt (fun ε : ℝ ↦ a * (k + 2 * ε)) 0 := by fun_prop
  have hc : ContinuousAt (fun ε : ℝ ↦ (k + ε) / (1 - a * ε)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
  have hI : ContinuousAt (fun ε : ℝ ↦ (k + 2 * ε) * (a / (1 - a * ε))) 0 := by
    apply ContinuousAt.mul
    · fun_prop
    · apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · norm_num
  have hB : ContinuousAt (fun ε : ℝ ↦ k + 2 * ε) 0 := by fun_prop
  have hU : ContinuousAt (fun ε : ℝ ↦ a / (1 - a * ε)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
  have hM : ∀ᶠ ε : ℝ in 𝓝 0, 0 < a → ρ < a⁻¹ - 3 * ε := by
    by_cases ha' : 0 < a
    · have hr : ρ < a⁻¹ := (lt_inv_comm₀ ha' hρ).mp ha
      have hcM : ContinuousAt (fun ε : ℝ ↦ -(a⁻¹ - 3 * ε)) 0 := by fun_prop
      filter_upwards [hcM.eventually_lt_const (show -(a⁻¹ - 3 * (0 : ℝ)) < -ρ by
        simpa using neg_lt_neg hr)] with ε hε
      intro _
      linarith
    · exact Filter.Eventually.of_forall (fun _ h ↦ (ha' h).elim)
  have hnear : ∀ᶠ ε : ℝ in 𝓝 0,
      2 * a * ε < 1 ∧
      a * (k + ε) / (1 - a * ε) ^ 2 < 1 ∧
      a * (k + ε) / (1 - 2 * a * ε) < 1 ∧
      a * (k + 2 * ε) / (1 - 2 * a * ε) < 1 ∧
      a * (k + 2 * ε) < 1 ∧
      (k + 2 * ε) * (a / (1 - a * ε)) < 1 ∧
      (k + ε) / (1 - a * ε) < ρ ∧ k + 2 * ε < ρ ∧
      a / (1 - a * ε) < ρ⁻¹ ∧ (0 < a → ρ < a⁻¹ - 3 * ε) := by
    filter_upwards [hlin.eventually_lt_const (show 2 * a * (0 : ℝ) < 1 by norm_num),
      hq₁.eventually_lt_const (by simpa using hak),
      hq₂.eventually_lt_const (by simpa using hak),
      hqJ.eventually_lt_const (by simpa using hak),
      hslope.eventually_lt_const (by simpa using hak),
      hI.eventually_lt_const (by simpa [mul_comm] using hak),
      hc.eventually_lt_const (by simpa using hk),
      hB.eventually_lt_const (by simpa using hk),
      hU.eventually_lt_const (by simpa using ha), hM] with ε h₀ h₁ h₂ h₃ h₄ hIε h₅ h₆ h₇ h₈
    exact ⟨h₀, h₁, h₂, h₃, h₄, hIε, h₅, h₆, h₇, h₈⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  have hmem : ε ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hε] using hεδ
  obtain ⟨h₀, h₁, h₂, h₃, h₄, hIε, h₅, h₆, h₇, h₈⟩ := hball hmem
  refine ⟨h₀, by nlinarith [mul_nonneg ha0 hε], by linarith,
    h₁, h₂, h₃, h₄, hIε, h₅, h₆, h₇, ?_, ?_, h₈⟩
  · intro hρ₁
    have hi : ρ⁻¹ ≤ 1 := by simpa using inv_le_one_of_one_le₀ hρ₁
    exact lt_min (h₇.trans_le hi) h₇
  · intro hρ₁
    have hv : k + ε < ρ := by linarith
    exact lt_min (hv.trans_le hρ₁) hv

end HolomorphicAnosov
