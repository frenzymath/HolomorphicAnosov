import HolomorphicAnosov.Analysis.Regularity.JournePlaqueHigherHolder
import HolomorphicAnosov.Analysis.CompositionHolderBound
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

/-- A uniform receiving-domain guard for recharting bounded plaques. -/
theorem holder_rechart_receiving_core
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) (hn : 1 ≤ n) (α K B R ρ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hR : 0 < R) (hρ : 0 < ρ) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ (U : Set D), IsOpen U → Convex ℝ U →
      ∀ (q : D → E) (g : E → F) (x : D) (a : E),
      HasFiniteHolderBounds n α K q U →
      HasFiniteHolderBounds n α B g (Metric.ball a ρ) →
      Metric.ball x R ⊆ U → q x ∈ Metric.ball a (ρ/2) →
      Metric.ball x r ⊆ U ∧ MapsTo q (Metric.ball x r) (Metric.ball a ρ) ∧
      HasFiniteHolderBounds n α C (g ∘ q) (Metric.ball x r) := by
  obtain ⟨M, hM, H⟩ := HolomorphicAnosov.composition_holder_bound n α hn hα hα1
  let r := min (R/2) (ρ/(2*(K+1)))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrR : r ≤ R := (min_le_left _ _).trans (by linarith)
  have hkr : K*r ≤ ρ/2 := by
    have hpos : 0 < 2*(K+1) := by positivity
    have h := (le_div_iff₀ hpos).mp (min_le_right (R/2) (ρ/(2*(K+1))))
    change r * (2*(K+1)) ≤ ρ at h
    nlinarith
  refine ⟨r, M*B*(1+K^((n:ℝ)+α)), hr, by positivity, ?_⟩
  intro U hU hcU q g x a hq hg hsub hx
  have hsmall : Metric.ball x r ⊆ U := (Metric.ball_subset_ball hrR).trans hsub
  have hxU : x ∈ U := hsub (Metric.mem_ball_self hR)
  have hdiff (z : D) (hz : z ∈ U) : DifferentiableAt ℝ q z :=
    (hq.1.contDiffAt (hU.mem_nhds hz)).differentiableAt (by exact_mod_cast (show n ≠ 0 by omega))
  have hDn (z : D) (hz : z ∈ U) : ‖fderiv ℝ q z‖ ≤ K := by
    simpa only [norm_iteratedFDeriv_one] using hq.2.1 1 hn z hz
  have hmap : MapsTo q (Metric.ball x r) (Metric.ball a ρ) := by
    intro z hz
    have hdist : ‖z-x‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
    have hcenter : ‖q x-a‖ < ρ/2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hlip := hcU.norm_image_sub_le_of_norm_fderiv_le hdiff hDn hxU (hsmall hz)
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖q z-a‖ ≤ ‖q z-q x‖ + ‖q x-a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ K*‖z-x‖ + ‖q x-a‖ := add_le_add hlip le_rfl
      _ < ρ := by nlinarith [mul_le_mul_of_nonneg_left hdist.le hK]
  obtain ⟨hsmooth, hjets, hholder⟩ := H D E F (Metric.ball x r) (Metric.ball a ρ) q g K B
    Metric.isOpen_ball (convex_ball _ _) Metric.isOpen_ball (convex_ball _ _)
    (hq.1.mono hsmall) hg.1 hmap hK hB
    (fun j hj z hz ↦ by
      rw [iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hz]
      exact hq.2.1 j hj z (hsmall hz))
    (fun j hj z hz ↦ by
      rw [iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hz]
      exact hg.2.1 j hj z hz)
    (fun z hz z' hz' ↦ by
      rw [iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hz,
        iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hz']
      exact hq.2.2 z (hsmall hz) z' (hsmall hz'))
    (fun z hz z' hz' ↦ by
      rw [iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hz,
        iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hz']
      exact hg.2.2 z hz z' hz')
  refine ⟨hsmall, hmap, hsmooth, ?_, ?_⟩
  · intro j hj z hz
    simpa only [iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hz] using hjets j hj z hz
  · intro z hz z' hz'
    simpa only [iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hz,
      iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hz'] using hholder z hz z' hz'

end HolomorphicAnosov.JourneLeafPolynomialApproximation
