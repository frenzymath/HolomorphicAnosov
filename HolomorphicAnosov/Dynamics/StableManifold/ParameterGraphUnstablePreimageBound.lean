import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov

/-- On a centered unit-slope graph, an image point controls its preimage by `a/(1-aε)` (HPS, pp.54–55, 58–60). -/
theorem parameter_graph_unstable_preimage_bound
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X ≃L[ℝ] U) (S : Y →L[ℝ] V) (G : X × Y → U × V)
    (hG : G 0 = 0) (a ε : NNReal)
    (hT : ‖T.symm.toContinuousLinearMap‖ ≤ a) (hsmall : (a : ℝ) * ε < 1)
    (hR : LipschitzWith ε (fun z ↦ G z - (T z.1, S z.2)))
    (s : X → Y) (hs0 : s 0 = 0) (hs : LipschitzWith 1 s) (x : X) :
    ‖(x,s x)‖ ≤ (a : ℝ) / (1 - (a : ℝ) * ε) * ‖G (x,s x)‖ := by
  let R : X × Y → U × V := fun z ↦ G z - (T z.1, S z.2)
  have hn : ‖(x,s x)‖ = ‖x‖ := by
    have hsn : ‖s x‖ ≤ ‖x‖ := by simpa [hs0] using hs.norm_sub_le x 0
    exact max_eq_left hsn
  have hr : ‖R (x,s x)‖ ≤ (ε : ℝ) * ‖(x,s x)‖ := by
    simpa only [R, hG, Prod.fst_zero, Prod.snd_zero, map_zero,
      show ((0 : U), (0 : V)) = (0 : U × V) from rfl, sub_zero, sub_self] using
      hR.norm_sub_le (x,s x) 0
  have he : T x = (G (x,s x)).1 - (R (x,s x)).1 := by
    dsimp [R]
    abel
  have hb : ‖(x,s x)‖ ≤ (a : ℝ) *
      (‖G (x,s x)‖ + (ε : ℝ) * ‖(x,s x)‖) := calc
    _ = ‖T.symm (T x)‖ := by rw [T.symm_apply_apply, hn]
    _ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T x‖ := T.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ (a : ℝ) * ‖T x‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg _)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ a.2
      rw [he]
      exact (norm_sub_le _ _).trans (add_le_add (norm_fst_le _)
        ((norm_fst_le _).trans hr))
  have hd : 0 < 1 - (a : ℝ) * ε := sub_pos.mpr hsmall
  apply (le_of_mul_le_mul_left ?_ hd : ‖(x,s x)‖ ≤ _)
  calc
    _ ≤ (a : ℝ) * ‖G (x,s x)‖ := by nlinarith only [hb]
    _ = (1 - (a : ℝ) * ε) *
        ((a : ℝ) / (1 - (a : ℝ) * ε) * ‖G (x,s x)‖) := by field_simp

end HolomorphicAnosov
