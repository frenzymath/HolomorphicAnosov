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

namespace HolomorphicAnosov.Analysis

open Set
open scoped ContDiff

/-- McMullen, Advanced Complex Analysis, Corollary 1.23 p.12 (Rouché straight-line homotopy).
Public auxiliary result in the regular-hypersurface proof. -/
lemma lebl_disk_zero_persistence {c : ℂ} {r : ℝ} (hr : 0 < r)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall c r))
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c r)) (hfc : f c = 0)
    (hb : ∀ z ∈ Metric.sphere c r, f z ≠ 0)
    (hclose : ∀ z ∈ Metric.sphere c r, ‖g z - f z‖ < ‖f z‖) :
    ∃ z ∈ Metric.ball c r, g z = 0 := by
  classical
  have hgb : ∀ z ∈ Metric.sphere c r, g z ≠ 0 := by
    intro z hz hgz
    have := hclose z hz
    simp [hgz] at this
  let γ₀ := HolomorphicAnosov.diskBoundaryLoop c r f hr hf.continuousOn
  let γ₁ := HolomorphicAnosov.diskBoundaryLoop c r g hr hg.continuousOn
  have hcircle : ∀ z : Circle, c + (r : ℂ) * (z : ℂ) ∈ Metric.sphere c r := by
    intro z
    rw [Metric.mem_sphere]
    simp [dist_eq_norm, Complex.norm_real, abs_of_pos hr, Circle.norm_coe]
  have hb₀ : ∀ z, γ₀ z ≠ 0 := fun z ↦ hb _ (hcircle z)
  have hb₁ : ∀ z, γ₁ z ≠ 0 := fun z ↦ hgb _ (hcircle z)
  let H : C(↑unitInterval × Circle, ℂ) :=
    ⟨fun tz ↦ γ₀ tz.2 + (tz.1 : ℝ) * (γ₁ tz.2 - γ₀ tz.2), by
      exact ((γ₀.continuous.comp continuous_snd).add
        ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
          ((γ₁.continuous.comp continuous_snd).sub
            (γ₀.continuous.comp continuous_snd))))⟩
  have hhom : HolomorphicAnosov.LoopHomotopyAvoids γ₀ γ₁ 0 := by
    refine ⟨H, ?_, ?_, ?_⟩
    · intro z; simp [H]
    · intro z; simp [H]
    · intro t z he
      have hdiff : ‖γ₁ z - γ₀ z‖ < ‖γ₀ z‖ := hclose _ (hcircle z)
      have htnorm : ‖((t : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg t.property.1]
        exact t.property.2
      have hn : ‖((t : ℝ) : ℂ) * (γ₁ z - γ₀ z)‖ < ‖γ₀ z‖ :=
        lt_of_le_of_lt (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) htnorm) hdiff
      have he' : ((t : ℝ) : ℂ) * (γ₁ z - γ₀ z) = -(γ₀ z) := by
        change γ₀ z + ((t : ℝ) : ℂ) * (γ₁ z - γ₀ z) = 0 at he
        linear_combination he
      rw [he', norm_neg] at hn
      exact (lt_irrefl _) hn
  have hw := HolomorphicAnosov.winding_holomorphic_zero_count.1 γ₀ γ₁ 0 hb₀ hb₁ hhom
  obtain ⟨s, hs, ho, hsum, hpre⟩ :=
    HolomorphicAnosov.winding_holomorphic_zero_count.2.2.2.2 c 0 r f hr hf hb
  have hcs : c ∈ s := (hs c).mpr ⟨Metric.mem_ball_self hr, hfc⟩
  have hpos : 0 < s.sum (fun x ↦ (analyticOrderNatAt (fun z ↦ f z - 0) x : ℤ)) := by
    apply Finset.sum_pos
    · intro x hx
      exact_mod_cast (ho x hx).2
    · exact ⟨c, hcs⟩
  have hwind : HolomorphicAnosov.loopWinding γ₁ 0 hb₁ ≠ 0 := by
    rw [← hw]
    exact ne_of_gt (by simpa [γ₀] using hsum ▸ hpos)
  obtain ⟨s', hs', ho', hsum', hpre'⟩ :=
    HolomorphicAnosov.winding_holomorphic_zero_count.2.2.2.2 c 0 r g hr hg hgb
  exact hpre' hwind

end HolomorphicAnosov.Analysis
