import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageStep
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageDerivative

/-!
# Affine representatives under the image graph transform

Source: Hirsch–Pugh–Shub, *Invariant Manifolds* (1977), pp.55–56, with the
differentiable-jet comparison on pp.33–34. Apply the graph-image construction
to a centered linear representative and differentiate the resulting graph.
-/

noncomputable section
namespace HolomorphicAnosov

/-- HPS pp.55–56 and the differentiable-jet comparison pp.33–34: the image
of an affine unit-slope representative, after translation of its anchor to
zero, has a centered unit-Lipschitz representative and the rational slope
derivative. Apply the original-norm image step to the linear input P; this
constructs the actual horizontal homeomorphism with its inverse bound and
the output graph. The graph derivative formula then gives the derivative at
zero whenever the horizontal derivative J is invertible. No differentiability
of the invariant graph is assumed, and the lower linear block may be singular.
The horizontal derivative equivalence is an explicit input, supplied by the
small-perturbation inverse calculation in the parent proof. -/
theorem parameter_graph_affine_image
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X ≃L[ℝ] U) (S : Y →L[ℝ] V)
    (G : X × Y → U × V) (hG : G 0 = 0)
    (a k ε : NNReal) (ha : ‖T.symm.toContinuousLinearMap‖ ≤ a) (hk : ‖S‖ ≤ k)
    (hsmall : (a : ℝ) * ε < 1)
    (hslope : (a : ℝ) * ((k : ℝ) + 2 * ε) ≤ 1)
    (hR : LipschitzWith ε (fun z ↦ G z - (T z.1, S z.2)))
    (P : X →L[ℝ] Y) (hP : ‖P‖ ≤ 1)
    (F : X × Y →L[ℝ] U × V) (hF : HasFDerivAt G F 0)
    (J : X ≃L[ℝ] U)
    (hJ : J.toContinuousLinearMap =
      (ContinuousLinearMap.fst ℝ U V).comp (F.comp ((ContinuousLinearMap.id ℝ X).prod P))) :
    ∃ H : X ≃ₜ U, ∃ s' : U → V,
      (∀ x, H x = (G (x,P x)).1) ∧ H 0 = 0 ∧
      (∀ u v, ‖H.symm u - H.symm v‖ ≤
        (a : ℝ) / (1 - (a : ℝ) * ε) * ‖u - v‖) ∧
      s' 0 = 0 ∧ LipschitzWith 1 s' ∧
      G '' Set.range (fun x ↦ (x,P x)) = Set.range (fun u ↦ (u,s' u)) ∧
      HasFDerivAt s'
        (((ContinuousLinearMap.snd ℝ U V).comp
          (F.comp ((ContinuousLinearMap.id ℝ X).prod P))).comp J.symm.toContinuousLinearMap)
        0 := by
  have hPlip : LipschitzWith 1 (P : X → Y) := P.lipschitzWith_of_opNorm_le hP
  obtain ⟨H, s', hH, hH0, hi, hs0, hs, himage⟩ :=
    parameter_graph_image_step T S G hG a k ε ha hk hsmall hslope hR P P.map_zero hPlip
  refine ⟨H, s', hH, hH0, hi, hs0, hs, himage, ?_⟩
  have hd := parameter_graph_image_derivative G P s' H hH himage 0 F P
    (by convert hF using 1; simp) (P.hasFDerivAt (x := 0)) J hJ
  simpa only [hH0] using hd

end HolomorphicAnosov
