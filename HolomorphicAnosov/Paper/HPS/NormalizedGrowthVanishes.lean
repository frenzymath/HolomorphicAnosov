import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Constructions

open Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov






theorem hps_normalized_growth_vanishes
    (d b : ℕ → ℝ) (L ρ C M : ℝ) (hρ : 0 < ρ) (hgap : ρ < L)
    (hC : 0 ≤ C) (hd : 0 ≤ d 0)
    (hstep : ∀ n, L * d n ≤ d (n + 1))
    (hcompare : ∀ n, d n ≤ C * b n)
    (hbound : ∀ n, b n / ρ ^ n ≤ M) : d 0 = 0 := by
  have hL : 0 < L := hρ.trans hgap
  have hgrowth : ∀ n, L ^ n * d 0 ≤ d n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          L ^ (n + 1) * d 0 = L * (L ^ n * d 0) := by rw [pow_succ]; ring
          _ ≤ L * d n := mul_le_mul_of_nonneg_left ih hL.le
          _ ≤ d (n + 1) := hstep n
  have hfinal (n : ℕ) : d 0 ≤ (C * M) * (ρ / L) ^ n := by
    have hb := (div_le_iff₀ (pow_pos hρ n)).mp (hbound n)
    have hh := (hgrowth n).trans ((hcompare n).trans
      (mul_le_mul_of_nonneg_left hb hC))
    calc
      d 0 ≤ (C * (M * ρ ^ n)) / L ^ n :=
        (le_div_iff₀ (pow_pos hL n)).mpr (by simpa only [mul_comm] using hh)
      _ = (C * M) * (ρ / L) ^ n := by rw [div_pow]; ring
  have hlim : Tendsto (fun n : ℕ ↦ (C * M) * (ρ / L) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hρ.le hL.le)
        ((div_lt_one hL).mpr hgap)).const_mul (C * M)
  exact le_antisymm (ge_of_tendsto' hlim hfinal) hd

end HolomorphicAnosov
