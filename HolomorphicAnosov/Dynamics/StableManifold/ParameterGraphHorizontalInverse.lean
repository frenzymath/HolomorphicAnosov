import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLinearPerturbation

noncomputable section
namespace HolomorphicAnosov

/-- HPS pp.55–58: horizontal inverses for both rational derivative graph
transforms in the original fibre norms. The derivative blocks satisfy
‖A−T‖≤ε, ‖B‖≤ε and ‖C‖≤ε. A unit source slope gives
‖A+BP−T‖≤2ε, and a unit receiving slope gives ‖A−PC−T‖≤2ε.
Apply the linear perturbation inverse theorem to each operator. This gives
the common inverse bound a/(1−2aε), including zero horizontal fibres.
No hypothesis on the lower diagonal block is required. -/
theorem parameter_graph_horizontal_inverse
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X ≃L[ℝ] U) (A : X →L[ℝ] U) (B : Y →L[ℝ] U) (C : X →L[ℝ] V)
    (a ε : NNReal) (ha : ‖T.symm.toContinuousLinearMap‖ ≤ a)
    (hsmall : 2 * (a : ℝ) * ε < 1)
    (hA : ‖A-T.toContinuousLinearMap‖ ≤ ε) (hB : ‖B‖ ≤ ε) (hC : ‖C‖ ≤ ε) :
    (∀ P : X →L[ℝ] Y, ‖P‖ ≤ 1 →
      ∃ J : X ≃L[ℝ] U, J.toContinuousLinearMap = A + B.comp P ∧
        ‖J.symm.toContinuousLinearMap‖ ≤ (a : ℝ) / (1 - 2 * (a : ℝ) * ε)) ∧
    (∀ P : V →L[ℝ] U, ‖P‖ ≤ 1 →
      ∃ J : X ≃L[ℝ] U, J.toContinuousLinearMap = A - P.comp C ∧
        ‖J.symm.toContinuousLinearMap‖ ≤ (a : ℝ) / (1 - 2 * (a : ℝ) * ε)) := by
  have hsmall' : (a : ℝ) * (↑(2*ε) : ℝ) < 1 := by
    convert hsmall using 1; push_cast; ring
  have hout (L : X →L[ℝ] U) (hL : ‖L-T.toContinuousLinearMap‖ ≤ (↑(2*ε) : ℝ)) :
      ∃ J : X ≃L[ℝ] U, J.toContinuousLinearMap = L ∧
        ‖J.symm.toContinuousLinearMap‖ ≤ (a : ℝ) / (1 - 2 * (a : ℝ) * ε) := by
    obtain ⟨J,hJ,hb⟩ := parameter_graph_linear_perturbation T L a (2*ε) ha hL hsmall'
    refine ⟨J,hJ,?_⟩
    convert hb using 1; push_cast; ring
  constructor
  · intro P hP
    apply hout
    have he : A + B.comp P - T.toContinuousLinearMap =
        (A-T.toContinuousLinearMap) + B.comp P := by abel
    rw [he]
    calc
      _ ≤ ‖A-T.toContinuousLinearMap‖ + ‖B.comp P‖ := norm_add_le _ _
      _ ≤ (ε : ℝ) + ‖B‖ * ‖P‖ := add_le_add hA (B.opNorm_comp_le P)
      _ ≤ (ε : ℝ) + (ε : ℝ) * 1 :=
        add_le_add le_rfl (mul_le_mul hB hP (norm_nonneg _) ε.2)
      _ = _ := by push_cast; ring
  · intro P hP
    apply hout
    have he : A - P.comp C - T.toContinuousLinearMap =
        (A-T.toContinuousLinearMap) - P.comp C := by abel
    rw [he]
    calc
      _ ≤ ‖A-T.toContinuousLinearMap‖ + ‖P.comp C‖ := norm_sub_le _ _
      _ ≤ (ε : ℝ) + ‖P‖ * ‖C‖ := add_le_add hA (P.opNorm_comp_le C)
      _ ≤ (ε : ℝ) + 1 * (ε : ℝ) :=
        add_le_add le_rfl (mul_le_mul hP hC (norm_nonneg _) (by norm_num))
      _ = _ := by push_cast; ring

end HolomorphicAnosov
