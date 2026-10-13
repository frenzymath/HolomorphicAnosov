import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHorizontalInverse
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeComparison

noncomputable section
namespace HolomorphicAnosov

/-- The closed unit ball of continuous linear slopes, with its inherited operator norm metric. -/
abbrev ParameterGraphUnitHom (X Y : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] :=
  {P : X →L[ℝ] Y // ‖P‖ ≤ 1}

/-- Both first-derivative slope transforms preserve the closed unit operator ball and contract there (HPS, pp.55–58). -/
theorem parameter_graph_slope_transform
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X ≃L[ℝ] U)
    (A : X →L[ℝ] U) (B : Y →L[ℝ] U) (C : X →L[ℝ] V) (D : Y →L[ℝ] V)
    (a k ε : NNReal)
    (ha : ‖T.symm.toContinuousLinearMap‖ ≤ a)
    (hA : ‖A - T.toContinuousLinearMap‖ ≤ ε)
    (hB : ‖B‖ ≤ ε) (hC : ‖C‖ ≤ ε) (hD : ‖D‖ ≤ (k : ℝ) + ε)
    (hsmall : 2 * (a : ℝ) * ε < 1)
    (hq : (a : ℝ) * (k + 2 * ε) / (1 - 2 * (a : ℝ) * ε) < 1) :
    ∃ q : NNReal,
      (q : ℝ) = (a : ℝ) * (k + 2 * ε) / (1 - 2 * (a : ℝ) * ε) ∧ q < 1 ∧
      ∃ (Φs : ParameterGraphUnitHom X Y → ParameterGraphUnitHom U V)
        (Φt : ParameterGraphUnitHom V U → ParameterGraphUnitHom Y X),
        LipschitzWith q Φs ∧ LipschitzWith q Φt ∧
        (∀ P, (Φs P).1.comp (A + B.comp P.1) = C + D.comp P.1 ∧
          ‖(Φs P).1‖ ≤ q) ∧
        (∀ P, (A - P.1.comp C).comp (Φt P).1 = P.1.comp D - B ∧
          ‖(Φt P).1‖ ≤ q) := by
  have hden : 0 < 1 - 2 * (a : ℝ) * ε := sub_pos.mpr hsmall
  let b : NNReal := ⟨(a : ℝ) / (1 - 2 * (a : ℝ) * ε), div_nonneg a.2 hden.le⟩
  let q : NNReal := b * (k + 2 * ε)
  have hqeq : (q : ℝ) = (a : ℝ) * (k + 2 * ε) / (1 - 2 * (a : ℝ) * ε) := by
    change (a : ℝ) / (1 - 2 * (a : ℝ) * ε) * ((k : ℝ) + 2 * ε) = _
    ring
  have hq1 : (q : ℝ) < 1 := hqeq ▸ hq
  have hqformula : (b : ℝ) * ((k : ℝ) + ε + ε) = q := by
    simp only [q, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat]
    ring
  have hinverses := parameter_graph_horizontal_inverse T A B C a ε ha hsmall hA hB hC
  have hI (P : ParameterGraphUnitHom X Y) :
      ∃ H : X ≃L[ℝ] U, H.toContinuousLinearMap = A + B.comp P.1 ∧
        ‖H.symm.toContinuousLinearMap‖ ≤ b := hinverses.1 P.1 P.2
  have hP (P : ParameterGraphUnitHom V U) :
      ∃ H : X ≃L[ℝ] U, H.toContinuousLinearMap = A - P.1.comp C ∧
        ‖H.symm.toContinuousLinearMap‖ ≤ b := hinverses.2 P.1 P.2
  choose HI hHI hHInorm using hI
  choose HP hHP hHPnorm using hP
  let S (P : ParameterGraphUnitHom X Y) : U →L[ℝ] V :=
    (C + D.comp P.1).comp (HI P).symm.toContinuousLinearMap
  let R (P : ParameterGraphUnitHom V U) : Y →L[ℝ] X :=
    (HP P).symm.toContinuousLinearMap.comp (P.1.comp D - B)
  have hSnorm (P : ParameterGraphUnitHom X Y) : ‖S P‖ ≤ q := by
    have hnum : ‖C + D.comp P.1‖ ≤ (k : ℝ) + ε + ε := calc
      _ ≤ ‖C‖ + ‖D.comp P.1‖ := norm_add_le _ _
      _ ≤ (ε : ℝ) + ‖D‖ * ‖P.1‖ := add_le_add hC (D.opNorm_comp_le _)
      _ ≤ _ := by nlinarith [P.2, norm_nonneg D, norm_nonneg P.1]
    calc
      _ ≤ ‖C + D.comp P.1‖ * ‖(HI P).symm.toContinuousLinearMap‖ :=
        (C + D.comp P.1).opNorm_comp_le _
      _ ≤ ((k : ℝ) + ε + ε) * b := by gcongr; exact hHInorm P
      _ = q := by rw [mul_comm]; exact hqformula
  have hRnorm (P : ParameterGraphUnitHom V U) : ‖R P‖ ≤ q := by
    have hnum : ‖P.1.comp D - B‖ ≤ (k : ℝ) + ε + ε := calc
      _ ≤ ‖P.1.comp D‖ + ‖B‖ := norm_sub_le _ _
      _ ≤ ‖P.1‖ * ‖D‖ + ε := add_le_add (P.1.opNorm_comp_le _) hB
      _ ≤ _ := by nlinarith [P.2, norm_nonneg D, norm_nonneg P.1]
    calc
      _ ≤ ‖(HP P).symm.toContinuousLinearMap‖ * ‖P.1.comp D - B‖ :=
        (HP P).symm.toContinuousLinearMap.opNorm_comp_le _
      _ ≤ (b : ℝ) * ((k : ℝ) + ε + ε) := by gcongr; exact hHPnorm P
      _ = q := hqformula
  have hSeq (P : ParameterGraphUnitHom X Y) :
      (S P).comp (A + B.comp P.1) = C + D.comp P.1 := by
    rw [← hHI P]
    ext x
    simp [S]
  have hReq (P : ParameterGraphUnitHom V U) :
      (A - P.1.comp C).comp (R P) = P.1.comp D - B := by
    rw [← hHP P]
    ext y
    simp [R]
  let Φs (P : ParameterGraphUnitHom X Y) : ParameterGraphUnitHom U V :=
    ⟨S P, (hSnorm P).trans hq1.le⟩
  let Φt (P : ParameterGraphUnitHom V U) : ParameterGraphUnitHom Y X :=
    ⟨R P, (hRnorm P).trans hq1.le⟩
  have hcomp := parameter_graph_slope_comparison A B C D b (k + ε) ε
    (by simpa using hD)
  refine ⟨q, hqeq, by exact_mod_cast hq1, Φs, Φt, ?_, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro P P'
    simp only [Subtype.dist_eq, dist_eq_norm]
    change ‖S P - S P'‖ ≤ (q : ℝ) * ‖P.1 - P'.1‖
    rw [← hqformula]
    exact hcomp.1 P.1 P'.1 (S P) (S P') (HI P) (hHI P) (hHInorm P)
      (hSeq P) (hSeq P') ((hSnorm P').trans hq1.le) hB
  · apply LipschitzWith.of_dist_le_mul
    intro P P'
    simp only [Subtype.dist_eq, dist_eq_norm]
    change ‖R P - R P'‖ ≤ (q : ℝ) * ‖P.1 - P'.1‖
    rw [← hqformula]
    exact hcomp.2 P.1 P'.1 (R P) (R P') (HP P) (hHP P) (hHPnorm P)
      (hReq P) (hReq P') ((hRnorm P').trans hq1.le) hC
  · exact fun P ↦ ⟨hSeq P, hSnorm P⟩
  · exact fun P ↦ ⟨hReq P, hRnorm P⟩

end HolomorphicAnosov
