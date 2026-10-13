import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! Straight chart segments give smooth replacements for C¹ curves in convex extended charts. -/

open Set MeasureTheory Bundle Filter Manifold
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology _root_.Topology

namespace HolomorphicAnosov
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- Under upper and lower metric comparisons with factor `r`, a C¹ curve in a convex extended chart
admits a smooth replacement with the same endpoints and length at most `r²` times its length.
(Petersen, Cor. 5.3.10, p.150; Thm 5.3.8, pp.148–150) -/
theorem c1_chart_segment_replacement
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (x : M) (r : ℝ≥0) {a b : ℝ} (hab : a < b)
    {c : ℝ → M} (hc : ContMDiffOn 𝓘(ℝ) I 1 c (Icc a b))
    {s : Set E} (hs : Convex ℝ s) (hst : s ⊆ (extChartAt I x).target)
    (hcs : MapsTo (extChartAt I x ∘ c) (Icc a b) s)
    (hsource : MapsTo c (Icc a b) (extChartAt I x).source)
    (L : E →L[ℝ] TangentSpace I x)
    (hupper : ∀ z ∈ s, ∀ v : E,
      ‖mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) z v‖ ≤
        r * ‖L v‖)
    (hlower : ∀ t ∈ Icc a b, ∀ v : TangentSpace I (c t),
      ‖L (mfderiv I 𝓘(ℝ, E) (extChartAt I x) (c t) v)‖ ≤ r * ‖v‖) :
    ∃ σ : ℝ → M, ContMDiffOn 𝓘(ℝ) I ∞ σ (Icc 0 1) ∧
      σ 0 = c a ∧ σ 1 = c b ∧
      pathELength I σ 0 1 ≤ (r : ℝ≥0∞) * r * pathELength I c a b := by
  let e := extChartAt I x
  let f := e ∘ c
  let η := ContinuousAffineMap.lineMap (R := ℝ) (f a) (f b)
  let σ := e.symm ∘ η
  have hη : ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) ∞ η :=
    contMDiff_iff_contDiff.mpr η.contDiff
  have hηs : MapsTo η (Icc 0 1) s := by
    simpa only [η, ContinuousAffineMap.coe_lineMap_eq] using
      hs.mapsTo_lineMap (hcs ⟨le_rfl, hab.le⟩) (hcs ⟨hab.le, le_rfl⟩)
  have hσ : ContMDiffOn 𝓘(ℝ) I ∞ σ (Icc 0 1) :=
    (contMDiffOn_extChartAt_symm x).comp hη.contMDiffOn (hηs.mono_right hst)
  refine ⟨σ, hσ, ?_, ?_, ?_⟩
  · simp [σ, η, f, ContinuousAffineMap.coe_lineMap_eq, e.left_inv (hsource ⟨le_rfl, hab.le⟩)]
  · simp [σ, η, f, ContinuousAffineMap.coe_lineMap_eq, e.left_inv (hsource ⟨hab.le, le_rfl⟩)]
  have hseg : pathELength I σ 0 1 ≤ (r : ℝ≥0∞) * ‖L (f b - f a)‖ₑ := by
    rw [pathELength_eq_lintegral_mfderivWithin_Icc]
    calc
      _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, (r : ℝ≥0∞) * ‖L (f b - f a)‖ₑ := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        have hd := mfderivWithin_comp t
          (mdifferentiableWithinAt_extChartAt_symm (hst (hηs ht)))
          (hη.contMDiffOn.mdifferentiableOn (by simp) t ht)
          (hηs.mono_right (hst.trans (extChartAt_target_subset_range x)))
          ((uniqueDiffOn_Icc zero_lt_one t ht).uniqueMDiffWithinAt)
        have hdη : mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) η (Icc 0 1) t 1 = f b - f a := by
          rw [mfderivWithin_eq_fderivWithin]
          change fderivWithin ℝ (AffineMap.lineMap (f a) (f b)) (Icc 0 1) t 1 = _
          rw [AffineMap.hasDerivWithinAt_lineMap.hasFDerivWithinAt.fderivWithin
            (uniqueDiffOn_Icc zero_lt_one t ht)]
          exact one_smul _ _
        change ‖mfderivWithin 𝓘(ℝ) I (e.symm ∘ η) (Icc 0 1) t 1‖ₑ ≤ _
        rw [hd]
        change ‖mfderivWithin 𝓘(ℝ, E) I e.symm (range I) (η t)
          (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) η (Icc 0 1) t 1)‖ₑ ≤ _
        rw [hdη]
        simpa only [← ofReal_norm, ENNReal.ofReal_mul r.coe_nonneg, ENNReal.ofReal_coe_nnreal]
          using ENNReal.ofReal_le_ofReal (hupper _ (hηs ht) (f b - f a))
      _ = _ := by simp
  have hf : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 f (Icc a b) :=
    (contMDiffOn_extChartAt (I := I) (x := x)).comp hc (fun t ht ↦ by
      change c t ∈ (chartAt H x).source
      simpa only [extChartAt_source] using hsource ht)
  have hLf : ContDiffOn ℝ 1 (L ∘ f) (Icc a b) :=
    L.contDiff.comp_contDiffOn (contMDiffOn_iff_contDiffOn.mp hf)
  have hchord := enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hLf hab.le
  have hch : ‖L (f b - f a)‖ₑ ≤ (r : ℝ≥0∞) * pathELength I c a b := by
    simp only [Function.comp_apply, ← map_sub] at hchord
    apply hchord.trans
    rw [pathELength_eq_lintegral_mfderivWithin_Icc,
      ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    have hd := mfderiv_comp_mfderivWithin t
      (mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hsource ht))
      (hc.mdifferentiableOn (by simp) t ht)
      ((uniqueDiffOn_Icc hab t ht).uniqueMDiffWithinAt)
    have hdl := (L.hasFDerivAt.comp_hasDerivWithinAt t
      ((contMDiffOn_iff_contDiffOn.mp hf).differentiableOn one_ne_zero t ht).hasDerivWithinAt).derivWithin (uniqueDiffOn_Icc hab t ht)
    rw [hdl]
    have hd' : derivWithin f (Icc a b) t =
        mfderiv I 𝓘(ℝ, E) e (c t) (mfderivWithin 𝓘(ℝ) I c (Icc a b) t 1) := by
      rw [← fderivWithin_derivWithin, ← mfderivWithin_eq_fderivWithin]
      exact congrArg (fun A ↦ A 1) hd
    rw [hd']
    simpa only [← ofReal_norm, ENNReal.ofReal_mul r.coe_nonneg, ENNReal.ofReal_coe_nnreal]
      using ENNReal.ofReal_le_ofReal (hlower t ht (mfderivWithin 𝓘(ℝ) I c (Icc a b) t 1))
  calc
    _ ≤ (r : ℝ≥0∞) * ‖L (f b - f a)‖ₑ := hseg
    _ ≤ (r : ℝ≥0∞) * ((r : ℝ≥0∞) * pathELength I c a b) := by gcongr
    _ = _ := (mul_assoc _ _ _).symm

end HolomorphicAnosov

