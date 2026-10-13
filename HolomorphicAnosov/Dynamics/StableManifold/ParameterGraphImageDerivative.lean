import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

noncomputable section
namespace HolomorphicAnosov

/-- HPS, *Invariant Manifolds*, pp.55–56: derivative of the image graph
transform. If `F=DG(x,s(x))`, `P=Ds(x)` and the horizontal derivative is the
linear equivalence J, then the output derivative at H(x) is
`π₂ ∘ F ∘ (Id,P) ∘ J⁻¹`. Differentiate the graph embedding and G; the
horizontal projection is the derivative of H. The existing homeomorphism
inverse derivative theorem gives DH⁻¹=J⁻¹. Graph image equality identifies
the output function with G₂∘(Id,s)∘H⁻¹, so the chain rule gives the formula.
Only differentiability at the tested source point is required. -/
theorem parameter_graph_image_derivative
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : X × Y → U × V) (s : X → Y) (s' : U → V)
    (H : X ≃ₜ U) (hH : ∀ x, H x = (G (x,s x)).1)
    (himage : G '' Set.range (fun x ↦ (x,s x)) = Set.range (fun u ↦ (u,s' u)))
    (x : X) (F : X × Y →L[ℝ] U × V) (P : X →L[ℝ] Y)
    (hG : HasFDerivAt G F (x,s x)) (hs : HasFDerivAt s P x)
    (J : X ≃L[ℝ] U)
    (hJ : J.toContinuousLinearMap =
      (ContinuousLinearMap.fst ℝ U V).comp (F.comp ((ContinuousLinearMap.id ℝ X).prod P))) :
    HasFDerivAt s'
      (((ContinuousLinearMap.snd ℝ U V).comp
        (F.comp ((ContinuousLinearMap.id ℝ X).prod P))).comp J.symm.toContinuousLinearMap)
      (H x) := by
  have hpair := (hasFDerivAt_id x).prodMk hs
  have hc := hG.comp (f := fun y ↦ (y,s y)) x hpair
  have hHd : HasFDerivAt H J.toContinuousLinearMap x := by
    rw [hJ]
    have he : (H : X → U) = fun y ↦ (G (y,s y)).1 := funext hH
    rw [he]
    exact hc.fst
  have hi : HasFDerivAt H.symm J.symm.toContinuousLinearMap (H x) := by
    apply H.toOpenPartialHomeomorph.hasFDerivAt_symm (Set.mem_univ _)
    change HasFDerivAt H J.toContinuousLinearMap (H.symm (H x))
    rw [H.symm_apply_apply]
    exact hHd
  have heq : s' = fun u ↦ (G (H.symm u,s (H.symm u))).2 := by
    funext u
    have hm : G (H.symm u,s (H.symm u)) ∈ Set.range (fun v ↦ (v,s' v)) := by
      rw [← himage]
      exact ⟨(H.symm u,s (H.symm u)),⟨H.symm u,rfl⟩,rfl⟩
    obtain ⟨v,hv⟩ := hm
    have hvu : v = u := by
      simpa only [Prod.fst, ← hH, H.apply_symm_apply] using congrArg Prod.fst hv
    simpa only [Prod.snd,hvu] using congrArg Prod.snd hv
  rw [heq]
  apply HasFDerivAt.comp (g := fun y ↦ (G (y,s y)).2) (H x) _ hi
  simpa only [H.symm_apply_apply, Function.comp_apply] using hc.snd

end HolomorphicAnosov
