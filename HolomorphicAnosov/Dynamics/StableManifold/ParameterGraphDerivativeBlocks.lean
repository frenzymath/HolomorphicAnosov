import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Operator.Prod

noncomputable section
namespace HolomorphicAnosov

/-- HPS pp.54–58: the derivative blocks of an ε-Lipschitz perturbation of
a split linear map satisfy ‖A−T‖,‖B‖,‖C‖,‖D−S‖≤ε in the original
operator norms. Differentiate the remainder and bound its derivative by
its Lipschitz constant. Evaluate that operator on (x,0) and (0,y), whose
maximum-product norms equal the input norms; project to either component
and take the operator norm. This includes zero fibres and requires no
invertibility or completeness. -/
theorem parameter_graph_derivative_blocks
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X →L[ℝ] U) (S : Y →L[ℝ] V) (G : X × Y → U × V)
    (ε : NNReal) (hR : LipschitzWith ε (fun z ↦ G z - (T z.1,S z.2)))
    (z : X × Y) (F : X × Y →L[ℝ] U × V) (hF : HasFDerivAt G F z) :
    ‖((ContinuousLinearMap.fst ℝ U V).comp F).comp
      (ContinuousLinearMap.inl ℝ X Y) - T‖ ≤ ε ∧
    ‖((ContinuousLinearMap.fst ℝ U V).comp F).comp
      (ContinuousLinearMap.inr ℝ X Y)‖ ≤ ε ∧
    ‖((ContinuousLinearMap.snd ℝ U V).comp F).comp
      (ContinuousLinearMap.inl ℝ X Y)‖ ≤ ε ∧
    ‖((ContinuousLinearMap.snd ℝ U V).comp F).comp
      (ContinuousLinearMap.inr ℝ X Y) - S‖ ≤ ε := by
  let L : X × Y →L[ℝ] U × V := T.prodMap S
  have hL : HasFDerivAt (fun z : X × Y ↦ (T z.1,S z.2)) L z := L.hasFDerivAt
  have hnorm : ‖F-L‖ ≤ ε := (hF.sub hL).le_of_lipschitz hR
  have hb (w : X × Y) : ‖(F-L) w‖ ≤ (ε : ℝ) * ‖w‖ :=
    ((F-L).le_opNorm w).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
  have hfirst (x : X) : ‖(F (x,0)).1 - T x‖ ≤ (ε : ℝ) * ‖x‖ := by
    have h := (norm_fst_le ((F-L) (x,0))).trans (hb (x,0))
    simpa [L] using h
  have hsecond (y : Y) : ‖(F (0,y)).1‖ ≤ (ε : ℝ) * ‖y‖ := by
    have h := (norm_fst_le ((F-L) (0,y))).trans (hb (0,y))
    simpa [L] using h
  have hthird (x : X) : ‖(F (x,0)).2‖ ≤ (ε : ℝ) * ‖x‖ := by
    have h := (norm_snd_le ((F-L) (x,0))).trans (hb (x,0))
    simpa [L] using h
  have hfourth (y : Y) : ‖(F (0,y)).2 - S y‖ ≤ (ε : ℝ) * ‖y‖ := by
    have h := (norm_snd_le ((F-L) (0,y))).trans (hb (0,y))
    simpa [L] using h
  exact ⟨ContinuousLinearMap.opNorm_le_bound _ ε.2 hfirst,
    ContinuousLinearMap.opNorm_le_bound _ ε.2 hsecond,
    ContinuousLinearMap.opNorm_le_bound _ ε.2 hthird,
    ContinuousLinearMap.opNorm_le_bound _ ε.2 hfourth⟩

end HolomorphicAnosov
