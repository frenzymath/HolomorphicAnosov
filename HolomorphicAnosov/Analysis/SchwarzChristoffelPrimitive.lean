import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
namespace HolomorphicAnosov.Analysis.MarkedRectangle
open Set

/-- The four reciprocal square-root factors have a global noncritical primitive on
 the upper half-plane. Source: Stein–Shakarchi, Complex Analysis, Chapter 8,
 Example 3 pp.233–234 and §4.5 pp.245–247; Bak–Newman pp.189–190.
 For each real prevertex the translated upper half-plane avoids the logarithm
 cut. Exponentiating minus half this logarithm gives a holomorphic nonzero
 reciprocal square-root factor. Their product times -i is holomorphic and
 nonzero. The convex-domain primitive theorem supplies one primitive on the
 entire upper half-plane. Openness upgrades its within derivatives to ordinary
 derivatives. Squaring each exponential and using exp(log z)=z yields the
 displayed reciprocal-polynomial square identity. No separation of prevertices
 is needed for these interior facts; they hold even for repeated prevertices. -/
theorem exists_schwarzChristoffel_primitive (x : Fin 4 → ℝ) :
    ∃ W : ℂ → ℂ, ∀ z : ℂ, 0 < z.im →
      HasDerivAt W
        (-Complex.I * ∏ j : Fin 4, Complex.exp (-Complex.log (z - (x j : ℂ)) / 2)) z ∧
      deriv W z ≠ 0 ∧
      (deriv W z) ^ 2 = -(∏ j : Fin 4, (z - (x j : ℂ)))⁻¹ := by
  let H : Set ℂ := {z | 0 < z.im}
  let G : ℂ → ℂ := fun z ↦
    -Complex.I * ∏ j : Fin 4, Complex.exp (-Complex.log (z - (x j : ℂ)) / 2)
  have hslit (z : ℂ) (hz : z ∈ H) (j : Fin 4) : z - (x j : ℂ) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa using ne_of_gt hz
  have hdiff : DifferentiableOn ℂ G H := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.fun_finsetProd
    intro j _
    exact (((differentiableAt_id.sub_const (x j : ℂ)).clog (hslit z hz j)).neg.div_const 2).cexp
  obtain ⟨W, hW⟩ := (convex_halfSpace_im_gt (0 : ℝ)).exists_forall_hasDerivWithinAt hdiff
  refine ⟨W, fun z hz ↦ ?_⟩
  have hopen : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  have hder := (hW z hz).hasDerivAt (hopen.mem_nhds hz)
  refine ⟨hder, ?_, ?_⟩
  · rw [hder.deriv]
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
      (Finset.prod_ne_zero_iff.mpr (fun _ _ ↦ Complex.exp_ne_zero _))
  · rw [hder.deriv]
    change (-Complex.I * ∏ j : Fin 4, Complex.exp (-Complex.log (z - (x j : ℂ)) / 2)) ^ 2 = _
    rw [mul_pow, neg_sq, Complex.I_sq]
    rw [← Finset.prod_pow]
    have hf (j : Fin 4) :
        Complex.exp (-Complex.log (z - (x j : ℂ)) / 2) ^ 2 = (z - (x j : ℂ))⁻¹ := by
      rw [← Complex.exp_nat_mul]
      norm_num
      rw [show (2 : ℂ) * (-Complex.log (z - (x j : ℂ)) / 2) =
        -Complex.log (z - (x j : ℂ)) by ring]
      rw [Complex.exp_neg, Complex.exp_log (Complex.slitPlane_ne_zero (hslit z hz j))]
    simp_rw [hf]
    simp

end HolomorphicAnosov.Analysis.MarkedRectangle
