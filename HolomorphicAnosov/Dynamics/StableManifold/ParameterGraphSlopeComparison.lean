import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov

/-- The image and full-preimage first-derivative graph transforms contract slopes by `b*(d+e)` under the stated block norm bounds (HPS, pp.55–58). -/
theorem parameter_graph_slope_comparison
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : X →L[ℝ] U) (B : Y →L[ℝ] U) (C : X →L[ℝ] V) (D : Y →L[ℝ] V)
    (b d e : NNReal) (hD : ‖D‖ ≤ d) :
    (∀ (P P' : X →L[ℝ] Y) (Q Q' : U →L[ℝ] V) (H : X ≃L[ℝ] U),
      H.toContinuousLinearMap = A + B.comp P → ‖H.symm.toContinuousLinearMap‖ ≤ b →
      Q.comp (A + B.comp P) = C + D.comp P →
      Q'.comp (A + B.comp P') = C + D.comp P' →
      ‖Q'‖ ≤ 1 → ‖B‖ ≤ e →
      ‖Q-Q'‖ ≤ ((b : ℝ) * ((d : ℝ)+e)) * ‖P-P'‖) ∧
    (∀ (P P' : V →L[ℝ] U) (Q Q' : Y →L[ℝ] X) (H : X ≃L[ℝ] U),
      H.toContinuousLinearMap = A - P.comp C → ‖H.symm.toContinuousLinearMap‖ ≤ b →
      (A - P.comp C).comp Q = P.comp D - B →
      (A - P'.comp C).comp Q' = P'.comp D - B →
      ‖Q'‖ ≤ 1 → ‖C‖ ≤ e →
      ‖Q-Q'‖ ≤ ((b : ℝ) * ((d : ℝ)+e)) * ‖P-P'‖) := by
  constructor
  · intro P P' Q Q' H hH hb hQ hQ' hq hB
    have he : (Q-Q').comp H.toContinuousLinearMap = (D-Q'.comp B).comp (P-P') := by
      ext x
      have h1 := DFunLike.congr_fun hQ x
      have h2 := DFunLike.congr_fun hQ' x
      simp only [ContinuousLinearMap.comp_apply, add_apply] at h1 h2
      simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub]
      have hx : H.toContinuousLinearMap x = A x + B (P x) := DFunLike.congr_fun hH x
      rw [hx, h1]
      rw [map_add] at h2 ⊢
      rw [eq_sub_of_add_eq h2]
      abel
    have he' : Q-Q' = ((D-Q'.comp B).comp (P-P')).comp H.symm.toContinuousLinearMap := by
      ext u
      have hu := DFunLike.congr_fun he (H.symm u)
      simpa using hu
    have hn : ‖D-Q'.comp B‖ ≤ (d : ℝ)+e := calc
      _ ≤ ‖D‖ + ‖Q'.comp B‖ := norm_sub_le _ _
      _ ≤ (d : ℝ) + ‖Q'‖ * ‖B‖ := add_le_add hD (Q'.opNorm_comp_le _)
      _ ≤ _ := by nlinarith [norm_nonneg Q',norm_nonneg B]
    rw [he']
    calc
      _ ≤ (‖D-Q'.comp B‖ * ‖P-P'‖) * ‖H.symm.toContinuousLinearMap‖ :=
        (((D-Q'.comp B).comp (P-P')).opNorm_comp_le _).trans
          (mul_le_mul_of_nonneg_right ((D-Q'.comp B).opNorm_comp_le _) (norm_nonneg _))
      _ ≤ (((d : ℝ)+e) * ‖P-P'‖) * b := by gcongr
      _ = _ := by ring
  · intro P P' Q Q' H hH hb hQ hQ' hq hC
    have he : H.toContinuousLinearMap.comp (Q-Q') = (P-P').comp (D+C.comp Q') := by
      ext y
      have h1 := DFunLike.congr_fun hQ y
      have h2 := DFunLike.congr_fun hQ' y
      simp only [ContinuousLinearMap.comp_apply, sub_apply] at h1 h2
      simp only [ContinuousLinearMap.comp_apply, add_apply,
        sub_apply, map_sub, map_add]
      have hx (x : X) : H.toContinuousLinearMap x = A x - P (C x) := DFunLike.congr_fun hH x
      rw [hx,hx]
      rw [sub_eq_iff_eq_add.mp h1, sub_eq_iff_eq_add.mp h2]
      abel
    have he' : Q-Q' = H.symm.toContinuousLinearMap.comp ((P-P').comp (D+C.comp Q')) := by
      ext y
      have hy := congrArg H.symm (DFunLike.congr_fun he y)
      simpa using hy
    have hn : ‖D+C.comp Q'‖ ≤ (d : ℝ)+e := calc
      _ ≤ ‖D‖ + ‖C.comp Q'‖ := norm_add_le _ _
      _ ≤ (d : ℝ) + ‖C‖ * ‖Q'‖ := add_le_add hD (C.opNorm_comp_le _)
      _ ≤ _ := by nlinarith [norm_nonneg C,norm_nonneg Q']
    rw [he']
    calc
      _ ≤ ‖H.symm.toContinuousLinearMap‖ * (‖P-P'‖ * ‖D+C.comp Q'‖) :=
        (H.symm.toContinuousLinearMap.opNorm_comp_le _).trans
          (mul_le_mul_of_nonneg_left ((P-P').opNorm_comp_le _) (norm_nonneg _))
      _ ≤ (b : ℝ) * (‖P-P'‖ * ((d : ℝ)+e)) := by gcongr
      _ = _ := by ring

end HolomorphicAnosov
