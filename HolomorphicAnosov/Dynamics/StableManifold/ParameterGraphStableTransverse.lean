import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov

/-- Horizontal deviation from an invariant unit-slope graph expands by at least `m - 3 * ε` (HPS, pp.58–59, inequality (3)). -/
theorem parameter_graph_stable_transverse
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X ≃L[ℝ] U) (S : Y →L[ℝ] V) (G : X × Y → U × V)
    (m : ℝ) (hm : 0 ≤ m) (ε : NNReal)
    (hT : m * ‖T.symm.toContinuousLinearMap‖ ≤ 1)
    (hR : LipschitzWith ε (fun z ↦ G z - (T z.1, S z.2)))
    (t : Y → X) (t' : V → U) (ht' : LipschitzWith 1 t')
    (hgraph : ∀ y, (G (t y, y)).1 = t' (G (t y, y)).2)
    (x : X) (y : Y) :
    (m - 3 * (ε : ℝ)) * ‖x - t y‖ ≤ ‖(G (x,y)).1 - t' (G (x,y)).2‖ := by
  let R : X × Y → U × V := fun z ↦ G z - (T z.1, S z.2)
  have hr : ‖R (x,y) - R (t y,y)‖ ≤ (ε : ℝ) * ‖x - t y‖ := by
    simpa only [R, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero,
      max_eq_left (norm_nonneg _)] using hR.norm_sub_le (x,y) (t y,y)
  have hv : ‖(G (x,y)).2 - (G (t y,y)).2‖ ≤ (ε : ℝ) * ‖x - t y‖ := by
    have he : (G (x,y)).2 - (G (t y,y)).2 = (R (x,y) - R (t y,y)).2 := by
      simp only [R, Prod.snd_sub]
      abel
    rw [he]
    exact (norm_snd_le _).trans hr
  have ht : ‖t' (G (x,y)).2 - t' (G (t y,y)).2‖ ≤ (ε : ℝ) * ‖x - t y‖ :=
    (show ‖t' (G (x,y)).2 - t' (G (t y,y)).2‖ ≤
      ‖(G (x,y)).2 - (G (t y,y)).2‖ by
        simpa using ht'.norm_sub_le (G (x,y)).2 (G (t y,y)).2).trans hv
  have hl : m * ‖x - t y‖ ≤ ‖T (x - t y)‖ := calc
    _ = m * ‖T.symm (T (x - t y))‖ := by rw [T.symm_apply_apply]
    _ ≤ m * (‖T.symm.toContinuousLinearMap‖ * ‖T (x - t y)‖) :=
      mul_le_mul_of_nonneg_left (T.symm.toContinuousLinearMap.le_opNorm _) hm
    _ ≤ ‖T (x - t y)‖ := by nlinarith [norm_nonneg (T (x - t y))]
  have he : T (x - t y) =
      ((G (x,y)).1 - t' (G (x,y)).2) +
      (t' (G (x,y)).2 - t' (G (t y,y)).2) - (R (x,y) - R (t y,y)).1 := by
    simp only [R, Prod.fst_sub, map_sub]
    rw [← hgraph]
    abel
  have hu : ‖T (x - t y)‖ ≤ ‖(G (x,y)).1 - t' (G (x,y)).2‖ +
      2 * (ε : ℝ) * ‖x - t y‖ := by
    rw [he]
    calc
      _ ≤ (‖(G (x,y)).1 - t' (G (x,y)).2‖ + (ε : ℝ) * ‖x - t y‖) +
          (ε : ℝ) * ‖x - t y‖ :=
        (norm_sub_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add le_rfl ht))
          ((norm_fst_le _).trans hr))
      _ = _ := by ring
  calc
    _ ≤ (m - 2 * (ε : ℝ)) * ‖x - t y‖ :=
      mul_le_mul_of_nonneg_right (by linarith [ε.2]) (norm_nonneg _)
    _ = m * ‖x - t y‖ - 2 * (ε : ℝ) * ‖x - t y‖ := by ring
    _ ≤ _ := sub_le_iff_le_add.mpr (hl.trans hu)

end HolomorphicAnosov
