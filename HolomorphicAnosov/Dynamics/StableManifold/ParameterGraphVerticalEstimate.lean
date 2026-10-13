import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Abel

noncomputable section
namespace HolomorphicAnosov

/-- A Lipschitz perturbation of a split linear map satisfies the corresponding vertical difference bound (HPS, pp.54–57). -/
theorem parameter_graph_vertical_estimate
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X →L[ℝ] U) (S : Y →L[ℝ] V) (G : X × Y → U × V)
    (k ε : NNReal) (hk : ‖S‖ ≤ k)
    (hR : LipschitzWith ε (fun z ↦ G z - (T z.1, S z.2)))
    (x x' : X) (y y' : Y) :
    ‖(G (x, y)).2 - (G (x', y')).2‖ ≤
      (k : ℝ) * ‖y - y'‖ + (ε : ℝ) * max ‖x - x'‖ ‖y - y'‖ := by
  let R : X × Y → U × V := fun z ↦ G z - (T z.1, S z.2)
  have he : (G (x, y)).2 - (G (x', y')).2 =
      S (y - y') + ((R (x, y)).2 - (R (x', y')).2) := by
    simp only [R, Prod.snd_sub, map_sub]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add ((S.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hk (norm_nonneg _)))
  apply (norm_snd_le (R (x, y) - R (x', y'))).trans
  simpa only [R, Prod.norm_def, Prod.fst_sub, Prod.snd_sub] using
    hR.norm_sub_le (x, y) (x', y')

end HolomorphicAnosov
