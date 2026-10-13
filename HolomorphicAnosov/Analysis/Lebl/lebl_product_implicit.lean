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

/-- Lebl, Tasty Bits of Several Complex Variables v3.4, §1.6 Theorem 1.6.2 p.36.
Public auxiliary result in the regular-hypersurface proof. -/
lemma lebl_product_implicit {n : ℕ}
    {O : Set ((Fin n → ℂ) × ℂ)} {H : ((Fin n → ℂ) × ℂ) → ℂ}
    (hO : IsOpen O) (hH : ContDiffOn ℂ ∞ H O) {p : (Fin n → ℂ) × ℂ}
    (hp : p ∈ O) (hHp : H p = 0)
    (hpartial : (fderiv ℂ H p ∘L ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ).IsInvertible) :
    ∃ (V : Set (Fin n → ℂ)) (s : ℝ) (g : (Fin n → ℂ) → ℂ),
      IsOpen V ∧ p.1 ∈ V ∧ 0 < s ∧ g p.1 = p.2 ∧ DifferentiableOn ℂ g V ∧
      MapsTo g V (Metric.ball p.2 s) ∧
      (∀ y ∈ V, ∀ w ∈ Metric.ball p.2 s, (y, w) ∈ O) ∧
      (∀ y ∈ V, ∀ w ∈ Metric.ball p.2 s, H (y, w) = 0 ↔ w = g y) := by
  have hC : ContDiffAt ℂ 1 H p := (hH.contDiffAt (hO.mem_nhds hp)).of_le (by simp)
  let g := hC.implicitFunction (by norm_num) hpartial
  have hgp : g p.1 = p.2 := hC.implicitFunction_apply_self (by norm_num) hpartial
  have hCg : ContDiffAt ℂ 1 g p.1 := hC.contDiffAt_implicitFunction (by norm_num) hpartial
  obtain ⟨A, hAN, hAg⟩ := hCg.contDiffOn (le_refl 1) (by simp)
  have heq := hC.eventually_apply_eq_iff_implicitFunction (by norm_num) hpartial
  have hboth : ∀ᶠ z in nhds p, z ∈ O ∧ (H z = 0 ↔ z.2 = g z.1) := by
    filter_upwards [hO.mem_nhds hp, heq] with z hz hh
    exact ⟨hz, by simpa [hHp, g, eq_comm] using hh⟩
  obtain ⟨s, hs, hsb⟩ := Metric.eventually_nhds_iff_ball.mp hboth
  have hgn : g ⁻¹' Metric.ball p.2 s ∈ nhds p.1 := by
    exact hCg.continuousAt.preimage_mem_nhds (by simpa [hgp] using Metric.ball_mem_nhds _ hs)
  have hparam := Filter.inter_mem hAN (Filter.inter_mem hgn (Metric.ball_mem_nhds p.1 hs))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hparam
  refine ⟨Metric.ball p.1 δ, s, g, Metric.isOpen_ball, Metric.mem_ball_self hδ,
    hs, hgp, ?_, ?_, ?_, ?_⟩
  · exact (hAg.mono fun y hy ↦ (hδsub hy).1).differentiableOn (by norm_num)
  · intro y hy
    exact (hδsub hy).2.1
  · intro y hy w hw
    apply (hsb (y,w) _).1
    rw [← ball_prod_same]
    exact ⟨(hδsub hy).2.2, hw⟩
  · intro y hy w hw
    apply (hsb (y,w) _).2
    rw [← ball_prod_same]
    exact ⟨(hδsub hy).2.2, hw⟩

end HolomorphicAnosov.Analysis
