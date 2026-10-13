import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeComparison

noncomputable section
namespace HolomorphicAnosov

/-- Varying the four derivative blocks by at most δ, while keeping the unit input slope fixed, varies the rational image or preimage output by at most 4bδ, where b bounds the horizontal inverse (HPS pp.32–35,55–58). -/
theorem parameter_graph_slope_spatial_comparison
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A A' : X →L[ℝ] U) (B B' : Y →L[ℝ] U)
    (C C' : X →L[ℝ] V) (D D' : Y →L[ℝ] V)
    (b δ : NNReal)
    (hA : ‖A-A'‖≤δ) (hB : ‖B-B'‖≤δ)
    (hC : ‖C-C'‖≤δ) (hD : ‖D-D'‖≤δ) :
    (∀ (P : X →L[ℝ] Y) (Q Q' : U →L[ℝ] V) (H : X ≃L[ℝ] U),
      ‖P‖≤1 → ‖Q'‖≤1 →
      H.toContinuousLinearMap=A+B.comp P → ‖H.symm.toContinuousLinearMap‖≤b →
      Q.comp (A+B.comp P)=C+D.comp P →
      Q'.comp (A'+B'.comp P)=C'+D'.comp P →
      ‖Q-Q'‖≤4*(b:ℝ)*δ) ∧
    (∀ (P : V →L[ℝ] U) (Q Q' : Y →L[ℝ] X) (H : X ≃L[ℝ] U),
      ‖P‖≤1 → ‖Q'‖≤1 →
      H.toContinuousLinearMap=A-P.comp C → ‖H.symm.toContinuousLinearMap‖≤b →
      (A-P.comp C).comp Q=P.comp D-B →
      (A'-P.comp C').comp Q'=P.comp D'-B' →
      ‖Q-Q'‖≤4*(b:ℝ)*δ) := by
  constructor
  · intro P Q Q' H hP hQ'n hH hb hQ hQ'
    let N := (C-C')+(D-D').comp P-Q'.comp ((A-A')+(B-B').comp P)
    have he : (Q-Q').comp H.toContinuousLinearMap=N := by
      rw [hH]
      dsimp [N]
      simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
        ContinuousLinearMap.comp_add] at hQ hQ' ⊢
      rw [eq_sub_of_add_eq hQ,eq_sub_of_add_eq hQ']
      abel
    have he' : Q-Q'=N.comp H.symm.toContinuousLinearMap := by
      ext u
      have hu := DFunLike.congr_fun he (H.symm u)
      simpa using hu
    have hDP : ‖(D-D').comp P‖≤δ :=
      ((D-D').opNorm_comp_le P).trans (by nlinarith [norm_nonneg (D-D')])
    have hBP : ‖(B-B').comp P‖≤δ :=
      ((B-B').opNorm_comp_le P).trans (by nlinarith [norm_nonneg (B-B')])
    have hAB : ‖(A-A')+(B-B').comp P‖≤2*(δ:ℝ) :=
      (norm_add_le _ _).trans (by linarith)
    have hQN : ‖Q'.comp ((A-A')+(B-B').comp P)‖≤2*(δ:ℝ) :=
      (Q'.opNorm_comp_le _).trans (by nlinarith [norm_nonneg ((A-A')+(B-B').comp P)])
    have hN : ‖N‖≤4*(δ:ℝ) :=
      (norm_sub_le _ _).trans (by
        have hn := norm_add_le (C-C') ((D-D').comp P)
        linarith)
    rw [he']
    calc
      _ ≤ ‖N‖*‖H.symm.toContinuousLinearMap‖ := N.opNorm_comp_le _
      _ ≤ (4*(δ:ℝ))*b := by gcongr
      _ = _ := by ring
  · intro P Q Q' H hP hQ'n hH hb hQ hQ'
    let N := P.comp (D-D')-(B-B')-((A-A')-P.comp (C-C')).comp Q'
    have he : H.toContinuousLinearMap.comp (Q-Q')=N := by
      rw [hH]
      dsimp [N]
      simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub] at hQ hQ' ⊢
      rw [sub_eq_iff_eq_add.mp hQ,sub_eq_iff_eq_add.mp hQ']
      abel
    have he' : Q-Q'=H.symm.toContinuousLinearMap.comp N := by
      ext y
      have hy := congrArg H.symm (DFunLike.congr_fun he y)
      simpa using hy
    have hPD : ‖P.comp (D-D')‖≤δ :=
      (P.opNorm_comp_le _).trans (by nlinarith [norm_nonneg (D-D')])
    have hPC : ‖P.comp (C-C')‖≤δ :=
      (P.opNorm_comp_le _).trans (by nlinarith [norm_nonneg (C-C')])
    have hAC : ‖(A-A')-P.comp (C-C')‖≤2*(δ:ℝ) :=
      (norm_sub_le _ _).trans (by linarith)
    have hNQ : ‖((A-A')-P.comp (C-C')).comp Q'‖≤2*(δ:ℝ) :=
      (((A-A')-P.comp (C-C')).opNorm_comp_le _).trans
        (by nlinarith [norm_nonneg ((A-A')-P.comp (C-C'))])
    have hN : ‖N‖≤4*(δ:ℝ) :=
      (norm_sub_le _ _).trans (by
        have hn := norm_sub_le (P.comp (D-D')) (B-B')
        linarith)
    rw [he']
    calc
      _ ≤ ‖H.symm.toContinuousLinearMap‖*‖N‖ := H.symm.toContinuousLinearMap.opNorm_comp_le _
      _ ≤ (b:ℝ)*(4*(δ:ℝ)) := by gcongr
      _ = _ := by ring

end HolomorphicAnosov
