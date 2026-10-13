import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Set MeasureTheory Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/-! Public radial primitive evaluation used by the scalar Bochner–Martinelli mass.

Source: Demailly, *Complex Analytic and Differential Geometry*, I §3.D,
pp.25–26, equation (3.21) and the evaluation of `I_m` immediately before (3.23).
The source omits the one-variable calculation. This agent-written proof supplies
the primitive, derivative, positivity, and limit steps needed by
`analysis.scalar_bm_regularized_radial_mass_g18`.
-/

/-- For `n ≥ 1`, the radial Bochner–Martinelli mass integral evaluates to `1/(2n)`.

Source: the polar-coordinate evaluation of `I_m` in Demailly, *Complex Analytic and
Differential Geometry*, June 21, 2012, I §3.D, p.26, immediately before (3.23).
The following agent-written calculation expands the omitted radial integration.
Set `H(r) = r^(2n)/(2n*(1+r²)^n)`. The power and quotient rules show that
`H'(r) = r^(2n-1)/(1+r²)^(n+1)`, which is nonnegative for `r > 0`.
Since `H(r) = (2n)⁻¹*(r²/(1+r²))^n`, its limit at infinity is `(2n)⁻¹`.
Also `H(0) = 0` because `n ≥ 1`. The improper fundamental theorem of calculus
for a nonnegative derivative therefore gives the stated integral.
-/
theorem scalar_bochnermartinelli_radial_primitive {n : ℕ} (hn : 1 ≤ n) :
    ∫ r : ℝ in Ioi 0, r ^ (2*n-1) / (1+r^2)^(n+1) = (2*n:ℝ)⁻¹ := by
    let H : ℝ → ℝ := fun r => r ^ (2*n) / ((2*n:ℝ) * (1+r^2)^n)
    have hderiv : ∀ x ∈ Ici (0:ℝ), HasDerivAt H
        (x ^ (2*n-1) / (1+x^2)^(n+1)) x := by
      intro x hx
      dsimp [H]
      have hden : (2*n:ℝ) * (1+x^2)^n ≠ 0 := by positivity
      have hp : HasDerivAt (fun r : ℝ => r ^ (2*n)) ((2*n:ℝ) * x^(2*n-1)) x := by
        simpa [Nat.cast_mul] using (hasDerivAt_pow (2*n) x)
      have hinner : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2*x) x := by
        convert (hasDerivAt_pow 2 x).const_add 1 using 1; ring
      have hq0' := (hasDerivAt_pow n (1+x^2)).comp x hinner
      have hq0 : HasDerivAt (fun r : ℝ => (1 + r ^ 2)^n)
          ((n:ℝ) * (1+x^2)^(n-1) * (2*x)) x := by
        simpa [Function.comp_def] using hq0'
      have hq : HasDerivAt (fun r : ℝ => (2*n:ℝ) * (1+r^2)^n)
          ((2*n:ℝ) * ((n:ℝ) * (1+x^2)^(n-1) * (2*x))) x :=
        hq0.const_mul (2*n:ℝ)
      have hdiv := hp.div hq hden
      convert hdiv using 1
      field_simp [hden]
      have hp1 : (1+x^2)^n = (1+x^2)^(n-1) * (1+x^2) := by
        rw [← pow_succ, Nat.sub_add_cancel hn]
      have hp2 : x^(2*n) = x^(2*n-1) * x := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2*n)]
      rw [hp1, hp2]
      rw [show n+1 = (n-1)+2 by omega, pow_add]
      ring
    have hpos : ∀ x ∈ Ioi (0:ℝ), 0 ≤ x ^ (2*n-1) / (1+x^2)^(n+1) := by
      intro x hx
      have hx0 : 0 ≤ x := le_of_lt hx
      positivity
    have hsq : Tendsto (fun r : ℝ => r ^ 2) atTop atTop :=
      tendsto_pow_atTop (by decide : 2 ≠ 0)
    have hdenTop : Tendsto (fun r : ℝ => 1 + r ^ 2) atTop atTop :=
      tendsto_const_nhds.add_atTop hsq
    have hinv : Tendsto (fun r : ℝ => (1+r^2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hdenTop
    have hratio : Tendsto (fun r : ℝ => r^2 / (1+r^2)) atTop (𝓝 1) := by
      have h' := hinv.const_sub 1
      have heq : ∀ r : ℝ, 1 - (1+r^2)⁻¹ = r^2 / (1+r^2) := by
        intro r
        field_simp
        ring
      simpa using h'.congr heq
    have hpow : Tendsto (fun r : ℝ => (r^2 / (1+r^2))^n) atTop (𝓝 1) := by
      simpa using hratio.pow n
    have hscaled := hpow.const_mul ((2*n:ℝ)⁻¹)
    have heq : ∀ r : ℝ, (2*n:ℝ)⁻¹ * (r^2 / (1+r^2))^n = H r := by
      intro r
      have hn0 : (2*n:ℝ) ≠ 0 := by positivity
      dsimp [H]
      field_simp [hn0]
      rw [div_pow]
      field_simp
      rw [pow_mul]
    have hlim : Tendsto H atTop (𝓝 ((2*n:ℝ)⁻¹)) := by
      simpa using hscaled.congr heq
    have h := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim
    have hn0 : (2*n:ℝ) ≠ 0 := by positivity
    have hz : (0:ℝ) ^ (2*n) = 0 := zero_pow (by omega : 2*n ≠ 0)
    simpa [H, hz] using h

end HolomorphicAnosov.Analysis
