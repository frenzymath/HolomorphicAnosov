import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov

/-- HPS, *Invariant Manifolds*, p.57: weighted contraction bound for the full
preimage graph transform. The two horizontal equations and unit slope of the
first graph give `D ≤ a (2 ε D + d ‖G₂(x′,y)‖)`. The supplied vertical bound controls the last norm by `(k+ε) ‖y‖`
(as follows from centering for a unit-slope preimage graph). Absorbing `2 a ε D`
gives the stated coefficient. The vertical linear map may be singular. -/
theorem parameter_graph_preimage_comparison
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X ≃L[ℝ] U) (S : Y →L[ℝ] V) (G : X × Y → U × V)
    (a k ε d : NNReal) (ha : ‖T.symm.toContinuousLinearMap‖ ≤ a)
    (hsmall : 2 * (a : ℝ) * ε < 1)
    (hR : LipschitzWith ε (fun z ↦ G z - (T z.1, S z.2)))
    (t t' : V → U) (ht : LipschitzWith 1 t)
    (htt' : ∀ v, ‖t v - t' v‖ ≤ (d : ℝ) * ‖v‖)
    (x x' : X) (y : Y)
    (hx : (G (x, y)).1 = t (G (x, y)).2)
    (hx' : (G (x', y)).1 = t' (G (x', y)).2)
    (hvertical : ‖(G (x', y)).2‖ ≤ ((k : ℝ) + ε) * ‖y‖) :
    ‖x - x'‖ ≤ (a : ℝ) * ((k : ℝ) + ε) / (1 - 2 * (a : ℝ) * ε) * d * ‖y‖ := by
  let R : X × Y → U × V := fun z ↦ G z - (T z.1, S z.2)
  have hr : ‖R (x,y) - R (x',y)‖ ≤ (ε : ℝ) * ‖x - x'‖ := by
    simpa only [R, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero,
      max_eq_left (norm_nonneg _)] using hR.norm_sub_le (x,y) (x',y)
  have hv : ‖(G (x,y)).2 - (G (x',y)).2‖ ≤ (ε : ℝ) * ‖x - x'‖ := by
    have he : (G (x,y)).2 - (G (x',y)).2 = (R (x,y) - R (x',y)).2 := by
      simp only [R, Prod.snd_sub]
      abel
    rw [he]
    exact (norm_snd_le _).trans hr
  have htn : ‖t (G (x,y)).2 - t' (G (x',y)).2‖ ≤
      (ε : ℝ) * ‖x - x'‖ + (d : ℝ) * (((k : ℝ) + ε) * ‖y‖) := by
    apply (norm_sub_le_norm_sub_add_norm_sub _ (t (G (x',y)).2) _).trans
    apply add_le_add
    · exact (by simpa using ht.norm_sub_le (G (x,y)).2 (G (x',y)).2 :
        ‖t (G (x,y)).2 - t (G (x',y)).2‖ ≤ ‖(G (x,y)).2 - (G (x',y)).2‖).trans hv
    · exact (htt' _).trans (mul_le_mul_of_nonneg_left hvertical d.2)
  have he : T (x - x') = (t (G (x,y)).2 - t' (G (x',y)).2) -
      (R (x,y) - R (x',y)).1 := by
    simp only [R, Prod.fst_sub, map_sub]
    rw [hx, hx']
    abel
  have hb : ‖x - x'‖ ≤ (a : ℝ) *
      (2 * (ε : ℝ) * ‖x - x'‖ + (d : ℝ) * (((k : ℝ) + ε) * ‖y‖)) := calc
    _ = ‖T.symm (T (x - x'))‖ := by rw [T.symm_apply_apply]
    _ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T (x - x')‖ := T.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ (a : ℝ) * ‖T (x - x')‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ a.2
      rw [he]
      have hh := (norm_sub_le _ _).trans (add_le_add htn ((norm_fst_le _).trans hr))
      linarith [hh]
  have hden : 0 < 1 - 2 * (a : ℝ) * ε := sub_pos.mpr hsmall
  apply (le_of_mul_le_mul_left ?_ hden : ‖x - x'‖ ≤ _)
  field_simp
  nlinarith [hb]

end HolomorphicAnosov
