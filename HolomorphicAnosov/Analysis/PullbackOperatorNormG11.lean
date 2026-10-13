import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section
open Set Metric
namespace HolomorphicAnosov

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A linear map from a finite dimensional real vector space into the complex plane has a finite operator norm for the norm pulled back through an injective linear map into a normed space; the norm gives the pointwise bound, is positive for a nonzero map, and scales by the absolute value of real scalars.

Source: Ghys (1995), Lemma 3.3 p.593, derivative normalization; pinned Mathlib Analysis/Normed/Operator/NNNorm.lean sSup_unitClosedBall_eq_norm and linear operator norm scaling.
DAG: analysis.pullback_operator_norm_g11.

Identify the source E with the range of the injective map J by its linear equivalence e. The range carries its subspace norm and is finite dimensional, so T=D∘e⁻¹ is continuous linear. Under e the set defined by ‖Jv‖≤1 becomes the closed unit ball in range(J); hence the displayed supremum equals the usual operator norm ‖T‖. Its finiteness, nonnegativity and pointwise bound are the corresponding operator-norm facts. If D is nonzero then T is nonzero, so its norm is positive. Replacing D by cD replaces T by cT, whose operator norm is |c|‖T‖. This also covers zero D, zero scalars and the zero dimensional source. -/
lemma pullback_operator_norm (J : E →ₗ[ℝ] F) (hJ : Function.Injective J)
    (D : E →ₗ[ℝ] ℂ) :
    ∃ N : ℝ, 0 ≤ N ∧
      N = sSup ((fun v ↦ ‖D v‖) '' {v | ‖J v‖ ≤ 1}) ∧
      (∀ v, ‖D v‖ ≤ N * ‖J v‖) ∧
      (D ≠ 0 → 0 < N) ∧
      (∀ c : ℝ, sSup ((fun v ↦ ‖c • D v‖) '' {v | ‖J v‖ ≤ 1}) = |c| * N) := by
  let e : E ≃ₗ[ℝ] J.range := LinearEquiv.ofInjective J hJ
  let T : J.range →L[ℝ] ℂ := (D.comp e.symm.toLinearMap).toContinuousLinearMap
  have he (v : E) : ‖e v‖ = ‖J v‖ := rfl
  have hT (v : E) : T (e v) = D v := by simp [T]
  have hset (c : ℝ) :
      (fun v ↦ ‖c • D v‖) '' {v | ‖J v‖ ≤ 1} =
        (fun w ↦ ‖(c • T) w‖) '' closedBall 0 1 := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨e v, ?_, ?_⟩
      · simpa [mem_closedBall_zero_iff, he] using hv
      · simp [hT]
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨v, rfl⟩ := e.surjective w
      refine ⟨v, ?_, ?_⟩
      · simpa [mem_closedBall_zero_iff, he] using hw
      · simp [hT]
  have hsup : sSup ((fun v ↦ ‖D v‖) '' {v | ‖J v‖ ≤ 1}) = ‖T‖ := by
    have hh := hset 1
    simp only [one_smul] at hh
    rw [hh]
    exact T.sSup_unitClosedBall_eq_norm
  refine ⟨‖T‖, T.opNorm_nonneg, hsup.symm, ?_, ?_, ?_⟩
  · intro v
    simpa only [hT, he] using T.le_opNorm (e v)
  · intro hD
    apply (norm_pos_iff (a := T)).mpr
    intro hzero
    apply hD
    ext v
    have hz := hT v
    simpa [hzero] using hz.symm
  · intro c
    rw [hset, ContinuousLinearMap.sSup_unitClosedBall_eq_norm, norm_smul, Real.norm_eq_abs]

end HolomorphicAnosov

