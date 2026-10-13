import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov

/-- HPS pp.54–55: the quantitative comparison of two image graphs over the same
receiving horizontal coordinate, in the original maximum product norm.

Write `R = G - (T,S)`. The unit slope of `s` and the weighted graph difference give
`‖s x - t y‖ ≤ ‖x-y‖ + d‖y‖`. Equality of the horizontal image coordinates then
bounds `‖x-y‖` by `a ε (‖x-y‖ + d‖y‖)`. Absorb the first term using `a ε < 1`.
The vertical image difference has bound `(k+ε)(‖x-y‖ + d‖y‖)`, which yields the
claimed comparison. There is no inverse or nonzero-rank assumption on `S`. -/
theorem parameter_graph_image_comparison
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X ≃L[ℝ] U) (S : Y →L[ℝ] V) (G : X × Y → U × V)
    (a k ε d : NNReal) (ha : ‖T.symm.toContinuousLinearMap‖ ≤ a) (hk : ‖S‖ ≤ k)
    (hsmall : (a : ℝ) * ε < 1)
    (hR : LipschitzWith ε (fun z ↦ G z - (T z.1, S z.2)))
    (s t : X → Y) (hs : LipschitzWith 1 s)
    (hst : ∀ y, ‖s y - t y‖ ≤ (d : ℝ) * ‖y‖)
    (x y : X) (hxy : (G (x, s x)).1 = (G (y, t y)).1) :
    ‖(G (x, s x)).2 - (G (y, t y)).2‖ ≤
      ((k : ℝ) + ε) / (1 - (a : ℝ) * ε) * d * ‖y‖ := by
  let R : X × Y → U × V := fun z ↦ G z - (T z.1, S z.2)
  let B : ℝ := ‖x - y‖ + (d : ℝ) * ‖y‖
  have hsy : ‖s x - t y‖ ≤ B := by
    have hsxy : ‖s x - s y‖ ≤ ‖x - y‖ := by simpa using hs.norm_sub_le x y
    exact (norm_sub_le_norm_sub_add_norm_sub (s x) (s y) (t y)).trans
      (add_le_add hsxy (hst y))
  have hpair : ‖(x, s x) - (y, t y)‖ ≤ B := by
    rw [Prod.norm_def]
    apply max_le
    · exact le_add_of_nonneg_right (mul_nonneg d.2 (norm_nonneg _))
    · exact hsy
  have hRb : ‖R (x, s x) - R (y, t y)‖ ≤ (ε : ℝ) * B :=
    (hR.norm_sub_le _ _).trans (mul_le_mul_of_nonneg_left hpair ε.2)
  have hhorizontal : T (x - y) = -((R (x, s x)).1 - (R (y, t y)).1) := by
    simp only [R, Prod.fst_sub, map_sub]
    rw [hxy]
    abel
  have hxbound : ‖x - y‖ ≤ (a : ℝ) * ε * B := calc
    ‖x - y‖ = ‖T.symm (T (x - y))‖ := by rw [T.symm_apply_apply]
    _ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T (x - y)‖ :=
      T.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ (a : ℝ) * ‖T (x - y)‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    _ ≤ (a : ℝ) * ((ε : ℝ) * B) := by
      apply mul_le_mul_of_nonneg_left _ a.2
      rw [hhorizontal, norm_neg]
      exact (norm_fst_le _).trans hRb
    _ = _ := by ring
  have hden : 0 < 1 - (a : ℝ) * ε := sub_pos.mpr hsmall
  have hB : B ≤ (d : ℝ) * ‖y‖ / (1 - (a : ℝ) * ε) := by
    apply (le_div_iff₀ hden).2
    dsimp only [B] at *
    nlinarith [hxbound]
  have hvert : (G (x, s x)).2 - (G (y, t y)).2 =
      S (s x - t y) + ((R (x, s x)).2 - (R (y, t y)).2) := by
    simp only [R, Prod.snd_sub, map_sub]
    abel
  calc
    _ ≤ ‖S (s x - t y)‖ + ‖(R (x, s x)).2 - (R (y, t y)).2‖ := by
      rw [hvert]
      exact norm_add_le _ _
    _ ≤ (k : ℝ) * B + (ε : ℝ) * B := by
      apply add_le_add
      · exact (S.le_opNorm _).trans (mul_le_mul hk hsy (norm_nonneg _) k.2)
      · exact (norm_snd_le _).trans hRb
    _ = ((k : ℝ) + ε) * B := by ring
    _ ≤ ((k : ℝ) + ε) * ((d : ℝ) * ‖y‖ / (1 - (a : ℝ) * ε)) :=
      mul_le_mul_of_nonneg_left hB (add_nonneg k.2 ε.2)
    _ = _ := by ring


end HolomorphicAnosov
