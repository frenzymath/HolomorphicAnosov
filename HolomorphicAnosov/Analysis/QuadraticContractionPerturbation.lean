import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace HolomorphicAnosov.FactOneFiniteEnergy

/-- A strict quadratic contraction survives one uniform relative perturbation
of its source and receiving quadratic forms. The same constants work for all
nonnegative energies and include zero energies. Agent scalar step for the
smooth adapted metric comparison in Hirsch–Pugh (1969), Theorem 3.1 p.148,
and Shub (1987), Proposition 4.2 pp.21–22.

Proof: choose θ<a<1 and δ>0 so that (1+δ)θ²≤a²(1−δ).
For example δ=(a²−θ²)/(2(a²+θ²+1)) is positive and smaller than one.
The three comparison inequalities give h_y≤a²h_x; take square roots.
The lower source comparison makes h_x nonnegative, including when Q_x=0. -/
theorem quadratic_contraction_perturbation
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ a δ : ℝ, θ < a ∧ a < 1 ∧ 0 < δ ∧ δ < 1 ∧
      ∀ Qx Qy hx hy : ℝ, 0 ≤ Qx → Qy ≤ θ ^ 2 * Qx →
        (1 - δ) * Qx ≤ hx → hy ≤ (1 + δ) * Qy →
          Real.sqrt hy ≤ a * Real.sqrt hx := by
  let a := (θ + 1) / 2
  have ha : θ < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have ha0 : 0 < a := lt_of_le_of_lt hθ ha
  have hgap : 0 < a ^ 2 - θ ^ 2 := by nlinarith
  let d := 2 * (a ^ 2 + θ ^ 2 + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  let δ := (a ^ 2 - θ ^ 2) / d
  have hδ : 0 < δ := div_pos hgap hd
  have hδ1 : δ < 1 := by
    apply (div_lt_one hd).2
    dsimp [d]
    nlinarith [sq_nonneg a, sq_nonneg θ]
  have hδeq : δ * d = a ^ 2 - θ ^ 2 := div_mul_cancel₀ _ hd.ne'
  have hcoeff : (1 + δ) * θ ^ 2 ≤ a ^ 2 * (1 - δ) := by
    dsimp [d] at hδeq
    nlinarith [mul_nonneg hδ.le (sq_nonneg a), mul_nonneg hδ.le (sq_nonneg θ)]
  refine ⟨a, δ, ha, ha1, hδ, hδ1, ?_⟩
  intro Qx Qy hx hy hQx hQ hlow hupp
  have hhx : 0 ≤ hx := (mul_nonneg (by linarith) hQx).trans hlow
  have hfinal : hy ≤ a ^ 2 * hx := calc
    hy ≤ (1 + δ) * Qy := hupp
    _ ≤ (1 + δ) * (θ ^ 2 * Qx) := mul_le_mul_of_nonneg_left hQ (by linarith)
    _ ≤ a ^ 2 * ((1 - δ) * Qx) := by nlinarith [mul_le_mul_of_nonneg_right hcoeff hQx]
    _ ≤ a ^ 2 * hx := mul_le_mul_of_nonneg_left hlow (sq_nonneg a)
  calc
    Real.sqrt hy ≤ Real.sqrt (a ^ 2 * hx) := Real.sqrt_le_sqrt hfinal
    _ = a * Real.sqrt hx := by rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha0.le]

end HolomorphicAnosov.FactOneFiniteEnergy
