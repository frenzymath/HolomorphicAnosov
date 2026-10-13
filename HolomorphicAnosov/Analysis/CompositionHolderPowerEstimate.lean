import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace HolomorphicAnosov

/-- The numerical absorption in de la Llave–Obaya Theorem 4.3(ii.3), p.170.
For a≤1 the linear term is bounded by one; for a≥1 it is bounded by a^(t+1).
Multiplicativity of nonnegative real powers then absorbs the scaled power term.
The zero-base case uses t≥0, so no cancellation or division by a is required. -/
theorem composition_holder_power_estimate (a b t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) :
    a * (1 + (b * a) ^ t) ≤ (1 + b ^ t) * (1 + a ^ (t + 1)) := by
  have hp : a ≤ 1 + a ^ (t + 1) := by
    by_cases ha1 : a ≤ 1
    · exact ha1.trans (le_add_of_nonneg_right (Real.rpow_nonneg ha _))
    · have ha1' : 1 ≤ a := le_of_not_ge ha1
      have he : a ≤ a ^ (t + 1) := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le ha1' (show (1 : ℝ) ≤ t + 1 by linarith)
      linarith
  have he : a * a ^ t = a ^ (t + 1) := by
    rw [Real.rpow_add_one' ha (by linarith)]
    ring
  rw [Real.mul_rpow hb ha]
  have hbt : 0 ≤ b ^ t := Real.rpow_nonneg hb _
  nlinarith [Real.rpow_nonneg ha (t + 1)]


end HolomorphicAnosov
