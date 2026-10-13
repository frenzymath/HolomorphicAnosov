import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageComparison

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov

/-- HPS pp.54–55 weighted graph-transform contraction coefficient.

Apply the preceding comparison at the two inverse horizontal solutions of the
same target `u`. The already established inverse bound gives
`‖y‖ ≤ a/(1-aε) ‖u‖`. Substitution gives exactly the source coefficient
`a(k+ε)/(1-aε)^2` for the current convention `k = sup ‖T₂‖`. -/
theorem parameter_graph_image_weighted_comparison
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
    (x y : X) (u : U)
    (hx : (G (x, s x)).1 = u) (hy : (G (y, t y)).1 = u)
    (hybound : ‖y‖ ≤ (a : ℝ) / (1 - (a : ℝ) * ε) * ‖u‖) :
    ‖(G (x, s x)).2 - (G (y, t y)).2‖ ≤
      ((a : ℝ) * ((k : ℝ) + ε) / (1 - (a : ℝ) * ε) ^ 2) * d * ‖u‖ := by
  have hden : 0 < 1 - (a : ℝ) * ε := sub_pos.mpr hsmall
  calc
    _ ≤ ((k : ℝ) + ε) / (1 - (a : ℝ) * ε) * d * ‖y‖ :=
      parameter_graph_image_comparison T S G a k ε d ha hk hsmall hR s t hs hst
        x y (hx.trans hy.symm)
    _ ≤ ((k : ℝ) + ε) / (1 - (a : ℝ) * ε) * d *
        ((a : ℝ) / (1 - (a : ℝ) * ε) * ‖u‖) :=
      mul_le_mul_of_nonneg_left hybound
        (mul_nonneg (div_nonneg (add_nonneg k.2 ε.2) hden.le) d.2)
    _ = _ := by
      field_simp



end HolomorphicAnosov
