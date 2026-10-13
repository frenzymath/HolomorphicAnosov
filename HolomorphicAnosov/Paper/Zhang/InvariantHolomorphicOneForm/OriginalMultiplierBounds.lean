import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

open Set

open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang


universe u

/-- An invertible complex-linear map acting by a scalar `mu` has `0 < ‖mu‖ < 1` if a positive
iterate strictly contracts every nonzero vector. (Zhang, Lemma 4.2) -/
theorem original_multiplier_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Nontrivial E]
    (A : E ≃L[ℂ] E) (mu : ℂ) (k : ℕ) (hk : 1 ≤ k)
    (hscalar : ∀ v, A v = mu • v)
    (hblock : ∀ v : E, v ≠ 0 → ‖(A : E → E)^[k] v‖ < ‖v‖) :
    0 < ‖mu‖ ∧ ‖mu‖ < 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hmu : mu ≠ 0 := by
    intro h
    have he : A v = A 0 := by rw [hscalar, h, zero_smul, map_zero]
    exact hv (A.injective he)
  have hp : ∀ n : ℕ, (A : E → E)^[n] v = mu ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hscalar, smul_smul]
      rw [pow_succ']
  have hlt := hblock v hv
  rw [hp k, norm_smul, norm_pow] at hlt
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hpow : ‖mu‖ ^ k < 1 := by nlinarith
  exact ⟨norm_pos_iff.mpr hmu,
    (pow_lt_one_iff_of_nonneg (norm_nonneg mu) (by omega)).mp hpow⟩


end HolomorphicAnosov.Paper.Zhang
