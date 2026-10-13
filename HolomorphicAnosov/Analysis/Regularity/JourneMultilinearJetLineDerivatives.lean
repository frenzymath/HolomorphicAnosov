import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Tactic

open scoped ContDiff
noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation

/-- The factorial-weighted diagonal multilinear polynomial has its prescribed line jets. (Journé, 1988) -/
theorem multilinear_jet_line_derivatives {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (T : (j : Fin (n + 1)) → ContinuousMultilinearMap ℝ (fun _ : Fin j.val ↦ E) ℝ)
    (v : E) :
    let Q : ℝ → ℝ := fun t ↦ ∑ j : Fin (n + 1),
      (j.val.factorial : ℝ)⁻¹ * T j (fun _ ↦ t • v)
    ContDiff ℝ ∞ Q ∧
      (∀ m : Fin (n + 1), iteratedDeriv m.val Q 0 = T m (fun _ ↦ v)) ∧
      ∀ t : ℝ, iteratedDeriv n Q t = T ⟨n, Nat.lt_succ_self n⟩ (fun _ ↦ v) := by
  classical
  dsimp only
  have hscale (t : ℝ) (j : Fin (n + 1)) :
      T j (fun _ ↦ t • v) = t ^ j.val * T j (fun _ ↦ v) := by
    rw [(T j).map_smul_univ]
    simp
  simp_rw [hscale]
  have hsmooth (j : Fin (n + 1)) : ContDiff ℝ ∞
      (fun t : ℝ ↦ (j.val.factorial : ℝ)⁻¹ * (t ^ j.val * T j (fun _ ↦ v))) :=
    contDiff_const.mul ((contDiff_id.pow _).mul contDiff_const)
  refine ⟨ContDiff.sum (fun j _ ↦ hsmooth j), ?_, ?_⟩
  · intro m
    rw [iteratedDeriv_fun_sum (fun j _ ↦ (hsmooth j).contDiffAt.of_le (by simp))]
    simp only [iteratedDeriv_const_mul_field, iteratedDeriv_mul_const_field,
      iteratedDeriv_fun_pow_zero]
    rw [Finset.sum_eq_single m]
    · simp [Nat.factorial_ne_zero]
    · intro b _ hbm
      have hb : m.val ≠ b.val := fun h ↦ hbm (Fin.ext h.symm)
      simp [hb]
    · simp
  · intro t
    rw [iteratedDeriv_fun_sum (fun j _ ↦ (hsmooth j).contDiffAt.of_le (by simp))]
    simp only [iteratedDeriv_const_mul_field, iteratedDeriv_mul_const_field, iteratedDeriv_pow]
    rw [Finset.sum_eq_single ⟨n, Nat.lt_succ_self n⟩]
    · simp [Nat.descFactorial_self, Nat.factorial_ne_zero]
    · intro b _ hb
      have hbn : b.val < n := by
        have hne : b.val ≠ n := fun h ↦ hb (Fin.ext h)
        omega
      simp [Nat.descFactorial_eq_zero_iff_lt.mpr hbn]
    · simp
end HolomorphicAnosov.JourneLeafPolynomialApproximation
