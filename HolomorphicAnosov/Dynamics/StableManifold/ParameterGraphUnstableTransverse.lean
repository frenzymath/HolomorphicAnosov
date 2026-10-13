import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphVerticalEstimate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace HolomorphicAnosov

/-- The vertical distance from an invariant graph contracts by at most `k+2ε` under the map (HPS, pp.58–59, inequality (4)). -/
theorem parameter_graph_unstable_transverse
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X →L[ℝ] U) (S : Y →L[ℝ] V) (G : X × Y → U × V)
    (k ε : NNReal) (hS : ‖S‖ ≤ k)
    (hR : LipschitzWith ε (fun z ↦ G z - (T z.1, S z.2)))
    (s : X → Y) (s' : U → V) (hs' : LipschitzWith 1 s')
    (hgraph : ∀ x, (G (x,s x)).2 = s' (G (x,s x)).1)
    (x : X) (y : Y) :
    ‖(G (x,y)).2 - s' (G (x,y)).1‖ ≤
      ((k : ℝ) + 2 * ε) * ‖y - s x‖ := by
  let R : X × Y → U × V := fun z ↦ G z - (T z.1, S z.2)
  have hr : ‖R (x,y) - R (x,s x)‖ ≤ (ε : ℝ) * ‖y - s x‖ := by
    simpa only [R, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero,
      max_eq_right (norm_nonneg _)] using hR.norm_sub_le (x,y) (x,s x)
  have hh : ‖(G (x,y)).1 - (G (x,s x)).1‖ ≤ (ε : ℝ) * ‖y - s x‖ := by
    have he : (G (x,y)).1 - (G (x,s x)).1 = (R (x,y) - R (x,s x)).1 := by
      simp only [R, Prod.fst_sub]
      abel
    rw [he]
    exact (norm_fst_le _).trans hr
  have hs : ‖s' (G (x,s x)).1 - s' (G (x,y)).1‖ ≤ (ε : ℝ) * ‖y - s x‖ := by
    rw [norm_sub_rev]
    exact (show ‖s' (G (x,y)).1 - s' (G (x,s x)).1‖ ≤
      ‖(G (x,y)).1 - (G (x,s x)).1‖ by
      simpa using hs'.norm_sub_le (G (x,y)).1 (G (x,s x)).1).trans hh
  have hv : ‖(G (x,y)).2 - (G (x,s x)).2‖ ≤
      ((k : ℝ) + ε) * ‖y - s x‖ := by
    simpa only [sub_self, norm_zero, max_eq_right (norm_nonneg _), add_mul] using
      parameter_graph_vertical_estimate T S G k ε hS hR x x y (s x)
  calc
    _ ≤ ‖(G (x,y)).2 - (G (x,s x)).2‖ +
        ‖(G (x,s x)).2 - s' (G (x,y)).1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ((k : ℝ) + ε) * ‖y - s x‖ + (ε : ℝ) * ‖y - s x‖ := by
      exact add_le_add hv (by simpa only [hgraph] using hs)
    _ = _ := by ring

end HolomorphicAnosov
