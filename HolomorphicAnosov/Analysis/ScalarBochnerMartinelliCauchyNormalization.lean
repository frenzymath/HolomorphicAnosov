import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

/-!
# One-coordinate Bochner–Martinelli normalization

Source: Demailly, *Complex Analytic and Differential Geometry* (2012), I §3.A (3.2),
p.21, and I §3.D, pp.26–27. The algebraic specialization below retains the product
complex volume measure and totalized diagonal values of the existing scalar formula.
DAG node: `analysis.scalar_bm_cauchy_normalization_g1`.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace HolomorphicAnosov.Analysis

/-- Demailly, *Complex Analytic and Differential Geometry* (2012), I §3.A (3.2), p.21,
and I §3.D, pp.26–27: normalization of the one-coordinate scalar kernel.

Proof. There is one coordinate, so the Euclidean radius is the norm of its difference.
The conjugate divided by that norm squared is the complex inverse, including at zero
under totalized division. The finite sum has one term, 0! = 1, and moving 1/π inside
the integral gives precisely the negative Cauchy kernel. This integral identity needs
no integrability premise because multiplication by a fixed complex scalar commutes
with the totalized Bochner integral. No change of volume measure is made. -/
theorem scalar_bochnerMartinelli_cauchy_normalization
    (a : Fin 1 → (Fin 1 → ℂ) → ℂ) (z : Fin 1 → ℂ) (j : Fin 1) :
    -((Nat.factorial (1 - 1) : ℂ) / (Real.pi : ℂ) ^ 1) *
        (∫ ζ : Fin 1 → ℂ, ∑ k : Fin 1,
          star (ζ k - z k) /
            (Real.sqrt (∑ l : Fin 1, ‖(ζ - z) l‖ ^ 2) : ℂ) ^ (2 * 1) * a k ζ) =
      -(∫ ζ : Fin 1 → ℂ, a j ζ / ((Real.pi : ℂ) * (ζ j - z j))) := by
  have hkernel (w : ℂ) : star w / (‖w‖ : ℂ) ^ 2 = w⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq]
    simp [div_eq_mul_inv]
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, pow_one, Fin.sum_univ_one,
    Pi.sub_apply, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), hkernel]
  rw [neg_mul, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ζ ↦ by simp [div_eq_mul_inv]; ring

end HolomorphicAnosov.Analysis
