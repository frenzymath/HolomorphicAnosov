import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHorizontalInverse
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Norm

noncomputable section
namespace HolomorphicAnosov

/-- HPS pp.55–58: the actual derivatives of two nonlinear preimage graphs
satisfy the rational slope equation. Differentiate the exact graph identity
through the graph embedding (t,id), and split the derivative of G into its
four original blocks. Uniqueness of the derivative gives AQ+B=P(CQ+D),
which rearranges to (A-PC)Q=PD-B. -/
theorem parameter_graph_preimage_derivative_equation
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : X × Y → U × V) (t : Y → X) (t' : V → U) (y : Y)
    (F : X × Y →L[ℝ] U × V) (hG : HasFDerivAt G F (t y,y))
    (ht : DifferentiableAt ℝ t y)
    (ht' : DifferentiableAt ℝ t' (G (t y,y)).2)
    (hgraph : ∀v,(G (t v,v)).1=t' (G (t v,v)).2)
    (A : X →L[ℝ] U) (B : Y →L[ℝ] U)
    (C : X →L[ℝ] V) (D : Y →L[ℝ] V)
    (hfirst : ∀x v,(F (x,v)).1=A x+B v)
    (hsecond : ∀x v,(F (x,v)).2=C x+D v) :
    (A-(fderiv ℝ t' (G (t y,y)).2).comp C).comp (fderiv ℝ t y) =
      (fderiv ℝ t' (G (t y,y)).2).comp D-B := by
  have hc := hG.comp (f := fun v ↦ (t v,v)) y
    (ht.hasFDerivAt.prodMk (hasFDerivAt_id y))
  have hr := ht'.hasFDerivAt.comp y hc.snd
  have hl := hc.fst
  dsimp only [Function.comp_def] at hl hr
  have heq : (fun v ↦ (G (t v,v)).1)=(fun v ↦ t' (G (t v,v)).2) := funext hgraph
  rw [heq] at hl
  have he := hl.unique hr
  ext v
  have hv := DFunLike.congr_fun he v
  change (F (fderiv ℝ t y v,v)).1 =
    fderiv ℝ t' (G (t y,y)).2 ((F (fderiv ℝ t y v,v)).2) at hv
  rw [hfirst,hsecond,map_add] at hv
  change A (fderiv ℝ t y v)-fderiv ℝ t' (G (t y,y)).2 (C (fderiv ℝ t y v)) =
    fderiv ℝ t' (G (t y,y)).2 (D v)-B v
  rw [eq_sub_of_add_eq hv]
  abel

/-- HPS pp.55–58: every solution of the preimage slope equation with unit
receiving slope obeys the strict interior bound q=a(k+2ε)/(1-2aε).
The original horizontal perturbation inverse gives J=A-PC and its bound.
The equation identifies Q=J inverse (PD-B); its numerator has norm at most
k+2ε. This proves the actual derivative lies strictly inside the unit ball
whenever q<1, including zero-dimensional horizontal fibres. -/
theorem parameter_graph_preimage_slope_interior
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X ≃L[ℝ] U)
    (A : X →L[ℝ] U) (B : Y →L[ℝ] U)
    (C : X →L[ℝ] V) (D : Y →L[ℝ] V)
    (a k ε : NNReal) (ha : ‖T.symm.toContinuousLinearMap‖≤a)
    (hA : ‖A-T.toContinuousLinearMap‖≤ε) (hB : ‖B‖≤ε)
    (hC : ‖C‖≤ε) (hD : ‖D‖≤(k:ℝ)+ε)
    (hsmall : 2*(a:ℝ)*ε<1)
    (hjet : (a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε)<1)
    (P : V →L[ℝ] U) (Q : Y →L[ℝ] X) (hP : ‖P‖≤1)
    (heq : (A-P.comp C).comp Q=P.comp D-B) :
    ‖Q‖≤(a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε) ∧ ‖Q‖<1 := by
  obtain ⟨J,hJ,hJn⟩ :=
    (parameter_graph_horizontal_inverse T A B C a ε ha hsmall hA hB hC).2 P hP
  have hQ : Q=J.symm.toContinuousLinearMap.comp (P.comp D-B) := by
    ext v
    have hv := DFunLike.congr_fun heq v
    rw [← hJ] at hv
    have hi := congrArg J.symm hv
    simpa using hi
  have hN : ‖P.comp D-B‖≤(k:ℝ)+2*ε := calc
    _ ≤ ‖P.comp D‖+‖B‖ := norm_sub_le _ _
    _ ≤ ‖P‖*‖D‖+ε := add_le_add (P.opNorm_comp_le _) hB
    _ ≤ _ := by nlinarith [norm_nonneg D]
  have hn : ‖Q‖≤(a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε) := by
    rw [hQ]
    calc
      _ ≤ ‖J.symm.toContinuousLinearMap‖*‖P.comp D-B‖ :=
        J.symm.toContinuousLinearMap.opNorm_comp_le _
      _ ≤ ((a:ℝ)/(1-2*(a:ℝ)*ε))*((k:ℝ)+2*ε) := by gcongr
      _ = _ := by ring
  exact ⟨hn,hn.trans_lt hjet⟩

/-- The actual derivative of a nonlinear preimage graph lies strictly inside
the unit slope ball under the quantitative graph-transform gap. Apply the
nonlinear derivative equation, the receiving graph's unit Lipschitz derivative
bound, and the rational interior estimate. HPS pp.32–35 and55–58. -/
theorem parameter_graph_preimage_derivative_interior
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : X × Y → U × V) (t : Y → X) (t' : V → U) (y : Y)
    (F : X × Y →L[ℝ] U × V) (hG : HasFDerivAt G F (t y,y))
    (ht : DifferentiableAt ℝ t y)
    (ht' : DifferentiableAt ℝ t' (G (t y,y)).2) (ht'L : LipschitzWith 1 t')
    (hgraph : ∀v,(G (t v,v)).1=t' (G (t v,v)).2)
    (T : X ≃L[ℝ] U)
    (A : X →L[ℝ] U) (B : Y →L[ℝ] U)
    (C : X →L[ℝ] V) (D : Y →L[ℝ] V)
    (hfirst : ∀x v,(F (x,v)).1=A x+B v)
    (hsecond : ∀x v,(F (x,v)).2=C x+D v)
    (a k ε : NNReal) (ha : ‖T.symm.toContinuousLinearMap‖≤a)
    (hA : ‖A-T.toContinuousLinearMap‖≤ε) (hB : ‖B‖≤ε)
    (hC : ‖C‖≤ε) (hD : ‖D‖≤(k:ℝ)+ε)
    (hsmall : 2*(a:ℝ)*ε<1)
    (hjet : (a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε)<1) :
    ‖fderiv ℝ t y‖≤(a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε) ∧ ‖fderiv ℝ t y‖<1 := by
  apply parameter_graph_preimage_slope_interior T A B C D a k ε ha hA hB hC hD
    hsmall hjet (fderiv ℝ t' (G (t y,y)).2) (fderiv ℝ t y)
  · exact norm_fderiv_le_of_lipschitz ℝ ht'L
  · exact parameter_graph_preimage_derivative_equation G t t' y F hG ht ht' hgraph
      A B C D hfirst hsecond

end HolomorphicAnosov
