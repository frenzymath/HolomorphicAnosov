import HolomorphicAnosov.Analysis.Complex.ProjectiveDeveloping.Helpers.ProjectiveInfinityOfNotFiniteSource
import HolomorphicAnosov.Geometry.ComplexProjectiveLine
import Mathlib.LinearAlgebra.Projectivization.Action
/-! Projective transformations fixing infinity act affinely in the finite chart. (Ghys, p. 600;
Demailly, V §15.A, p. 277) -/

namespace HolomorphicAnosov
open scoped ContDiff

/-- A projective transformation fixing infinity acts affinely on finite points. (Ghys, p. 600;
Demailly, V §15.A, p. 277) -/
theorem projective_fixed_infinity_affine
    (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
    (hfix : g • complexProjectiveLineInfinity = complexProjectiveLineInfinity) :
    ∃ α β : ℂ, ∀ z : ℂ,
      complexProjectiveLineChartFun 1 (g • complexProjectiveLineFinite z) 0 = α * z + β := by
  induction g using QuotientGroup.induction_on with
  | H A =>
    simp only [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk] at hfix ⊢
    have h10 : (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
      unfold complexProjectiveLineInfinity complexProjectiveLineChartInv
        complexProjectiveLineMk at hfix
      rw [Projectivization.matrixSpecialLinearGroup_smul_def, Projectivization.smul_mk] at hfix
      obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp hfix
      have h := congrFun ht 1
      change (t • complexProjectiveLineChartVector 0 0) 1 =
        Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) ℂ)
          (complexProjectiveLineChartVector 0 0) 1 at h
      symm
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        complexProjectiveLineChartVector, Pi.smul_apply, smul_eq_mul] using h
    refine ⟨(A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 / A 1 1,
      (A : Matrix (Fin 2) (Fin 2) ℂ) 0 1 / A 1 1, ?_⟩
    intro z
    unfold complexProjectiveLineFinite complexProjectiveLineChartInv
    rw [Projectivization.matrixSpecialLinearGroup_smul_def]
    change complexProjectiveLineChartFun 1 (A.toLin'_equiv •
      Projectivization.mk ℂ _ _) 0 = _
    rw [Projectivization.smul_mk]
    rw [show Projectivization.mk ℂ _ _ = complexProjectiveLineMk _ _ from rfl]
    rw [projective_fun_mk]
    change (Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) ℂ)
      (complexProjectiveLineChartVector 1 (fun _ ↦ z)) 0) /
      (Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) ℂ)
      (complexProjectiveLineChartVector 1 (fun _ ↦ z)) 1) = _
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, complexProjectiveLineChartVector, h10]
    ring
/-- A projective point away from infinity is reconstructed from its finite coordinate. -/
theorem projective_finite_chart_reconstruct (p : ComplexProjectiveLine)
    (hp : p ≠ complexProjectiveLineInfinity) :
    complexProjectiveLineFinite (complexProjectiveLineChartFun 1 p 0) = p := by
  have hs : p ∈ complexProjectiveLineChartSource 1 := by
    by_contra hn
    exact hp (Ghys.developing_eq_infinity_of_not_finite_source p hn)
  change complexProjectiveLineChartInv 1 _ = p
  convert projective_left_inv 1 p hs using 1
  congr 1

/-- The finite coordinate separates projective points away from infinity. -/
theorem projective_finite_chart_injective {p q : ComplexProjectiveLine}
    (hp : p ≠ complexProjectiveLineInfinity) (hq : q ≠ complexProjectiveLineInfinity)
    (h : complexProjectiveLineChartFun 1 p 0 = complexProjectiveLineChartFun 1 q 0) : p = q := by
  rw [← projective_finite_chart_reconstruct p hp, h, projective_finite_chart_reconstruct q hq]

/-- The finite-chart action of a projective transformation fixing infinity is affine. (Ghys, p. 600;
Demailly, V §15.A, p. 277) -/
theorem projective_fixed_infinity_chart_affine
    (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
    (hfix : g • complexProjectiveLineInfinity = complexProjectiveLineInfinity) :
    ∃ α β : ℂ, ∀ p : ComplexProjectiveLine, p ≠ complexProjectiveLineInfinity →
      complexProjectiveLineChartFun 1 (g • p) 0 =
        α * complexProjectiveLineChartFun 1 p 0 + β := by
  obtain ⟨α, β, h⟩ := projective_fixed_infinity_affine g hfix
  refine ⟨α, β, fun p hp ↦ ?_⟩
  have he := h (complexProjectiveLineChartFun 1 p 0)
  rwa [projective_finite_chart_reconstruct p hp] at he
end HolomorphicAnosov

