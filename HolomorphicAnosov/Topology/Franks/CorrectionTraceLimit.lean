import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic

open Filter
open scoped Topology _root_.Topology BigOperators

namespace HolomorphicAnosov

/-- The correction-trace estimate in Manning's count argument (1974), pp.425–426,
as supplied from physical boundary counts in FranksManning Step 11(C3).
An eventual bound by a strictly smaller exponential rate makes a correction
trace vanish when normalized by the principal rate. Divide the bound by the
positive principal-rate power and squeeze by C times a geometric sequence.
Only eventual bounds are required; the rate zero and the constant zero are allowed. -/
theorem franks_manning_correction_trace_limit
    (u : ℕ → ℂ) (C r ρ : ℝ) (hr : 0 ≤ r) (hgap : r < ρ)
    (hbound : ∀ᶠ m in atTop, ‖u m‖ ≤ C * r ^ m) :
    Tendsto (fun m ↦ u m / (ρ : ℂ) ^ m) atTop (𝓝 0) := by
  have hρ : 0 < ρ := lt_of_le_of_lt hr hgap
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg hr hρ.le) ((div_lt_one hρ).mpr hgap)
  apply squeeze_zero_norm' (a := fun m ↦ C * (r / ρ) ^ m) _
    (by simpa only [mul_zero] using hpow.const_mul C)
  filter_upwards [hbound] with m hm
  have hnorm : ‖u m / (ρ : ℂ) ^ m‖ = ‖u m‖ / ρ ^ m := by
    simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  rw [hnorm, div_pow, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hm (pow_nonneg hρ.le m)

/-- The finitely many signed correction traces have normalized sum tending to
zero. Manning (1974), p.425, equation (1), and FranksManning Step 11(C3–C4c).
Each term has its own strict exponential bound; multiplication by its fixed
sign preserves the zero limit, and so does a finite sum. The weights may be
arbitrary complex constants, in particular the integer signs in the exact
count formula. An empty correction family contributes zero. -/
theorem franks_manning_signed_corrections_limit
    {ι : Type*} (s : Finset ι) (u : ι → ℕ → ℂ) (ε : ι → ℂ)
    (C r : ι → ℝ) (ρ : ℝ)
    (hr : ∀ i ∈ s, 0 ≤ r i) (hgap : ∀ i ∈ s, r i < ρ)
    (hbound : ∀ i ∈ s, ∀ᶠ m in atTop, ‖u i m‖ ≤ C i * r i ^ m) :
    Tendsto (fun m ↦ (∑ i ∈ s, ε i * u i m) / (ρ : ℂ) ^ m)
      atTop (𝓝 0) := by
  have hi (i : ι) (his : i ∈ s) :=
    (franks_manning_correction_trace_limit (u i) (C i) (r i) ρ
      (hr i his) (hgap i his) (hbound i his)).const_mul (ε i)
  convert tendsto_finsetSum s hi using 1 <;>
    simp [div_eq_mul_inv, Finset.sum_mul, mul_assoc]

/-- A principal normalized trace tending to one and finitely many exponentially
smaller signed corrections give normalized physical count tending to one.
This is the limit passage in Manning (1974), equation (2), and the explicit
Step 11(C4c) source argument. The exact signed count identity is a hypothesis;
this theorem does not produce a Markov partition or the physical boundary bound. -/
theorem franks_manning_count_limit_of_signed_traces
    {ι : Type*} (s : Finset ι) (p N : ℕ → ℂ) (u : ι → ℕ → ℂ) (ε : ι → ℂ)
    (C r : ι → ℝ) (ρ : ℝ)
    (hr : ∀ i ∈ s, 0 ≤ r i) (hgap : ∀ i ∈ s, r i < ρ)
    (hbound : ∀ i ∈ s, ∀ᶠ m in atTop, ‖u i m‖ ≤ C i * r i ^ m)
    (hp : Tendsto (fun m ↦ p m / (ρ : ℂ) ^ m) atTop (𝓝 1))
    (hcount : ∀ m, N m = p m + ∑ i ∈ s, ε i * u i m) :
    Tendsto (fun m ↦ N m / (ρ : ℂ) ^ m) atTop (𝓝 1) := by
  have hc := franks_manning_signed_corrections_limit s u ε C r ρ hr hgap hbound
  simpa only [hcount, add_div, add_zero] using hp.add hc

/-- The real physical-count form of the same signed-trace limit. Taking real
parts of the complex normalized count identity supplies exactly the real limit
needed by the finite-basic-set count sum in Step 11(C4c). -/
theorem franks_manning_real_count_limit_of_signed_traces
    {ι : Type*} (s : Finset ι) (p : ℕ → ℂ) (N : ℕ → ℝ)
    (u : ι → ℕ → ℂ) (ε : ι → ℂ) (C r : ι → ℝ) (ρ : ℝ)
    (hr : ∀ i ∈ s, 0 ≤ r i) (hgap : ∀ i ∈ s, r i < ρ)
    (hbound : ∀ i ∈ s, ∀ᶠ m in atTop, ‖u i m‖ ≤ C i * r i ^ m)
    (hp : Tendsto (fun m ↦ p m / (ρ : ℂ) ^ m) atTop (𝓝 1))
    (hcount : ∀ m, (N m : ℂ) = p m + ∑ i ∈ s, ε i * u i m) :
    Tendsto (fun m ↦ N m / ρ ^ m) atTop (𝓝 1) := by
  have ht := franks_manning_count_limit_of_signed_traces s p
    (fun m ↦ (N m : ℂ)) u ε C r ρ hr hgap hbound hp hcount
  simpa only [Function.comp_def, ← Complex.ofReal_pow, ← Complex.ofReal_div,
    Complex.ofReal_re, Complex.one_re] using (Complex.continuous_re.tendsto 1).comp ht

end HolomorphicAnosov

