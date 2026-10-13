import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-!
This file records constancy of polynomial derivatives at and above the degree (Journé, 1988).
-/ 

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation

/-- 189–190, equations (5)–(7). (Journé, 1988) -/
theorem multilinear_top_derivative_const
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m n : ℕ} (hmn : m ≤ n)
    (P : ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F)
    (x y : Fin m → E) : iteratedFDeriv ℝ n P x = iteratedFDeriv ℝ n P y := by
  classical
  rcases hmn.eq_or_lt with rfl | hlt
  · rw [P.iteratedFDeriv_eq]
    change ∑ e : Fin m ↪ Fin m, _ = ∑ e : Fin m ↪ Fin m, _
    apply Finset.sum_congr rfl
    intro e _
    congr 1
    funext i
    exact False.elim (i.property ((Finite.surjective_of_injective e.injective) i.val))
  · have hz (z : Fin m → E) : iteratedFDeriv ℝ n P z = 0 := by
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      have H := P.norm_iteratedFDeriv_le n z
      simpa only [Fintype.card_fin,Nat.descFactorial_eq_zero_iff_lt.mpr hlt,
        Nat.cast_zero,zero_mul] using H
    rw [hz x,hz y]

/-- 189–190, equations (5)–(7). (Journé, 1988) -/
theorem multilinear_polynomial_top_derivative_const
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m n : ℕ} (hmn : m ≤ n)
    (P : ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F)
    (L : D →L[ℝ] (Fin m → E)) (x y : D) :
    iteratedFDeriv ℝ n (P ∘ L) x = iteratedFDeriv ℝ n (P ∘ L) y := by
  rw [L.iteratedFDeriv_comp_right (P.contDiff : ContDiff ℝ n P) x le_rfl,
    L.iteratedFDeriv_comp_right (P.contDiff : ContDiff ℝ n P) y le_rfl,
    multilinear_top_derivative_const hmn P (L x) (L y)]

end HolomorphicAnosov.JourneLeafPolynomialApproximation
