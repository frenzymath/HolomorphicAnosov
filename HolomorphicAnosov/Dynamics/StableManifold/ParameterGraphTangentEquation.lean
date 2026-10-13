import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp

noncomputable section
namespace HolomorphicAnosov

/-- Differentiating the invariant horizontal graph equation at the zero section gives a linear intertwining equation (HPS, Corollary 5.3, p.60). -/
theorem parameter_graph_tangent_equation
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X →L[ℝ] U) (S : Y →L[ℝ] V) (G : X × Y → U × V)
    (hG : G 0 = 0) (hDG : HasFDerivAt G (T.prodMap S) 0)
    (s : X → Y) (s' : U → V) (hs0 : s 0 = 0)
    (hs : DifferentiableAt ℝ s 0) (hs' : DifferentiableAt ℝ s' 0)
    (hgraph : ∀ x, (G (x,s x)).2 = s' (G (x,s x)).1) :
    S.comp (fderiv ℝ s 0) = (fderiv ℝ s' 0).comp T := by
  have hpair := (hasFDerivAt_id (0 : X)).prodMk hs.hasFDerivAt
  have hDG' : HasFDerivAt G (T.prodMap S) (0,s 0) := by
    simpa only [hs0, show (0,0) = (0 : X × Y) from rfl] using hDG
  have hcompose := hDG'.comp 0 hpair
  have hleft : HasFDerivAt (fun x ↦ (G (x,s x)).2) (S.comp (fderiv ℝ s 0)) 0 := by
    convert hcompose.snd using 1 <;> ext x <;> rfl
  have hfirst : HasFDerivAt (fun x ↦ (G (x,s x)).1) T 0 := by
    convert hcompose.fst using 1 <;> ext x <;> rfl
  have hright : HasFDerivAt (fun x ↦ s' (G (x,s x)).1)
      ((fderiv ℝ s' 0).comp T) 0 := by
    apply HasFDerivAt.comp 0 _ hfirst
    simpa only [hs0, show (0,0) = (0 : X × Y) from rfl, hG, Prod.fst_zero] using
      hs'.hasFDerivAt
  have heq : (fun x ↦ (G (x,s x)).2) = (fun x ↦ s' (G (x,s x)).1) := funext hgraph
  rw [heq] at hleft
  exact hleft.unique hright

end HolomorphicAnosov
