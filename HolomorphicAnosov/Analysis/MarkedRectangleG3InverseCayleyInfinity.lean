import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Complex.Basic

/-! Inverse-Cayley limits at the two real infinities. This is the finite-disk
continuity route corresponding to Bak--Newman, *Complex Analysis* (3rd ed.,
2010), p.190. -/

open Filter
open scoped Topology _root_.Topology
noncomputable section
namespace HolomorphicAnosov.Analysis.MarkedRectangle

/-- The inverse Cayley map `N(t)=(t-i)/(t+i)` tends to the boundary point `1`
along either real infinity. The proof factors by `t⁻¹`, uses the standard
inverse limits, and clears the nonzero real denominator pointwise. -/
theorem inverseCayley_real_tendsto_one {l : Filter ℝ}
    (hinv : Tendsto (fun t : ℝ ↦ t⁻¹) l (𝓝 0))
    (hne : ∀ᶠ t in l, t ≠ 0) :
    Tendsto (fun t : ℝ ↦ ((t : ℂ) - Complex.I) / ((t : ℂ) + Complex.I)) l (𝓝 1) := by
  have hi : Tendsto (fun t : ℝ ↦ ((t⁻¹ : ℝ) : ℂ)) l (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hinv
  have hlim : Tendsto (fun t : ℝ ↦
      (1 - Complex.I * ((t⁻¹ : ℝ) : ℂ)) / (1 + Complex.I * ((t⁻¹ : ℝ) : ℂ))) l (𝓝 1) := by
    have h1 : Tendsto (fun _ : ℝ ↦ (1 : ℂ)) l (𝓝 1) := tendsto_const_nhds
    have hiC : Tendsto (fun _ : ℝ ↦ Complex.I) l (𝓝 Complex.I) := tendsto_const_nhds
    have hh := (h1.sub (hiC.mul hi)).div (h1.add (hiC.mul hi))
      (by norm_num : (1 : ℂ) + Complex.I * 0 ≠ 0)
    convert hh using 1 ; simp
  apply hlim.congr'
  filter_upwards [hne] with t ht
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  push_cast
  field_simp

end HolomorphicAnosov.Analysis.MarkedRectangle

