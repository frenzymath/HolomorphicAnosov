import HolomorphicAnosov.Analysis.RudinDominatedRangeHahnBanach
import HolomorphicAnosov.Analysis.RudinL1DualBoundedRepresentative
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.Compact

/-!
Representation of bounded complex-linear functionals on continuous functions over a compact
Hausdorff space by a finite positive regular Borel measure and a bounded density. (Rudin, Thm 6.19,
pp. 130–132)
-/

open MeasureTheory

namespace HolomorphicAnosov

/-- Every bounded complex-linear functional on `C(K, ℂ)` for compact Hausdorff `K` is integration
against a finite positive regular Borel measure and a measurable density of norm at most one.
The measure has total mass equal to the operator norm, and each represented product is
integrable. (Rudin, Thm 6.19, pp. 130–132) -/
theorem rudin_compact_complex_riesz_density
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K]
    (Φ : C(K, ℂ) →L[ℂ] ℂ) :
    ∃ (μ : Measure K) (g : K → ℂ),
      IsFiniteMeasure μ ∧
      μ.Regular ∧
      Measurable g ∧
      (∀ x : K, ‖g x‖ ≤ 1) ∧
      (μ Set.univ).toReal = ‖Φ‖ ∧
      ∀ u : C(K, ℂ),
        Integrable (fun x => u x * g x) μ ∧
        Φ u = ∫ x, u x * g x ∂μ := by
  by_cases hΦ : Φ = 0
  · subst Φ
    refine ⟨0, fun _ ↦ 0, inferInstance, inferInstance, measurable_const, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro u
      simp
  have hc : 0 < ‖Φ‖ := lt_of_le_of_ne Φ.opNorm_nonneg
    (Ne.symm (fun hz ↦ hΦ ((ContinuousLinearMap.opNorm_zero_iff Φ).mp hz)))
  let Ψ : C(K, ℂ) →L[ℂ] ℂ := (‖Φ‖⁻¹ : ℂ) • Φ
  have hΨ : ‖Ψ‖ = 1 := by
    simp [Ψ, norm_smul, ne_of_gt hc]
  
  let A (a : C(K, ℝ)) : Set ℝ :=
    {r | ∃ u : C(K, ℂ), (∀ x, ‖u x‖ ≤ a x) ∧ r = ‖Ψ u‖}
  let L (a : C(K, ℝ)) : ℝ := sSup (A a)
  have hA_nonempty (a : C(K, ℝ)) (ha : ∀ x, 0 ≤ a x) : (A a).Nonempty := by
    refine ⟨0, 0, ?_, ?_⟩
    · simpa using ha
    · simp
  have hA_bound (a : C(K, ℝ)) (r : ℝ) (hr : r ∈ A a) : r ≤ ‖a‖ := by
    obtain ⟨u, hu, rfl⟩ := hr
    have hnorm : ‖u‖ ≤ ‖a‖ := (ContinuousMap.norm_le _ (norm_nonneg a)).mpr
      (fun x ↦ (hu x).trans ((le_abs_self (a x)).trans (a.norm_coe_le_norm x)))
    calc
      ‖Ψ u‖ ≤ ‖Ψ‖ * ‖u‖ := Ψ.le_opNorm u
      _ = ‖u‖ := by rw [hΨ, one_mul]
      _ ≤ ‖a‖ := hnorm
  have hA_bdd (a : C(K, ℝ)) : BddAbove (A a) := ⟨‖a‖, hA_bound a⟩
  have hL_nonneg (a : C(K, ℝ)) (ha : ∀ x, 0 ≤ a x) : 0 ≤ L a := by
    apply le_csSup (hA_bdd a)
    refine ⟨0, ?_, ?_⟩
    · simpa using ha
    · simp
  have hL_bound (a : C(K, ℝ)) (ha : ∀ x, 0 ≤ a x) : L a ≤ ‖a‖ :=
    csSup_le (hA_nonempty a ha) (hA_bound a)
  have hL_zero : L 0 = 0 := by
    exact le_antisymm (by simpa using hL_bound 0 (by simp))
      (hL_nonneg 0 (by simp))
  have hL_mono (a b : C(K, ℝ)) (ha : ∀ x, 0 ≤ a x)
      (hab : ∀ x, a x ≤ b x) : L a ≤ L b := by
    apply csSup_le_csSup (hA_bdd b) (hA_nonempty a ha)
    rintro r ⟨u, hu, rfl⟩
    exact ⟨u, fun x ↦ (hu x).trans (hab x), rfl⟩
  have hL_dominates (u : C(K, ℂ)) :
      ‖Ψ u‖ ≤ L ⟨fun x ↦ ‖u x‖, u.continuous.norm⟩ := by
    apply le_csSup (hA_bdd _)
    exact ⟨u, fun _ ↦ le_rfl, rfl⟩
  
  
  have hL_smul_lower (a : C(K, ℝ)) (ha : ∀ x, 0 ≤ a x)
      (c : ℝ) (hc0 : 0 ≤ c) : c * L a ≤ L (c • a) := by
    rcases eq_or_lt_of_le hc0 with rfl | hcpos
    · simp [hL_zero]
    rw [mul_comm c (L a)]
    apply (le_div_iff₀ hcpos).mp
    apply csSup_le (hA_nonempty a ha)
    rintro r ⟨u, hu, rfl⟩
    apply (le_div_iff₀ hcpos).mpr
    have hscale : ‖Ψ (c • u)‖ ≤ L (c • a) := by
      apply le_csSup (hA_bdd _)
      refine ⟨c • u, ?_, rfl⟩
      intro x
      change ‖c • u x‖ ≤ c * a x
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
      exact mul_le_mul_of_nonneg_left (hu x) hc0
    simpa only [ContinuousLinearMap.map_smul_of_tower, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hc0, mul_comm] using hscale
  have hL_smul (a : C(K, ℝ)) (ha : ∀ x, 0 ≤ a x)
      (c : ℝ) (hc0 : 0 ≤ c) : L (c • a) = c * L a := by
    rcases eq_or_lt_of_le hc0 with rfl | hcpos
    · simp [hL_zero]
    apply le_antisymm _ (hL_smul_lower a ha c hc0)
    have hreverse := hL_smul_lower (c • a)
      (fun x ↦ mul_nonneg hc0 (ha x)) c⁻¹ (inv_nonneg.mpr hc0)
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hcpos), one_smul] at hreverse
    calc
      L (c • a) = c * (c⁻¹ * L (c • a)) := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul]
      _ ≤ c * L a := mul_le_mul_of_nonneg_left hreverse hc0
  
  have hL_add_lower (a b : C(K, ℝ)) (ha : ∀ x, 0 ≤ a x)
      (hb : ∀ x, 0 ≤ b x) : L a + L b ≤ L (a + b) := by
    apply (le_sub_iff_add_le).mp
    apply csSup_le (hA_nonempty a ha)
    rintro r ⟨u, hu, rfl⟩
    apply (le_sub_iff_add_le).mpr
    rw [add_comm]
    apply (le_sub_iff_add_le).mp
    apply csSup_le (hA_nonempty b hb)
    rintro r ⟨v, hv, rfl⟩
    apply (le_sub_iff_add_le).mpr
    obtain ⟨c, hc, hcu⟩ := Complex.exists_norm_eq_mul_self (Ψ u)
    obtain ⟨d, hd, hdv⟩ := Complex.exists_norm_eq_mul_self (Ψ v)
    have hadm : ∀ x, ‖(c • u + d • v) x‖ ≤ (a + b) x := by
      intro x
      change ‖c * u x + d * v x‖ ≤ a x + b x
      calc
        _ ≤ ‖c * u x‖ + ‖d * v x‖ := norm_add_le _ _
        _ = ‖u x‖ + ‖v x‖ := by rw [norm_mul, norm_mul, hc, hd, one_mul, one_mul]
        _ ≤ _ := add_le_add (hu x) (hv x)
    have hval : Ψ (c • u + d • v) = ((‖Ψ u‖ + ‖Ψ v‖ : ℝ) : ℂ) := by
      simp only [map_add, map_smul, smul_eq_mul, ← hcu, ← hdv, Complex.ofReal_add]
    have hle : ‖Ψ (c • u + d • v)‖ ≤ L (a + b) :=
      le_csSup (hA_bdd _) ⟨_, hadm, rfl⟩
    rw [hval, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] at hle
    simpa only [add_comm] using hle
  -- The quotient is zero at common zeros; its norm bound by `‖u‖` ensures continuity there.
  
  have hpiece (a b : C(K, ℝ)) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
      (u : C(K, ℂ)) (hu : ∀ x, ‖u x‖ ≤ a x + b x) :
      ∃ v : C(K, ℂ), (∀ x, v x = (a x / (a x + b x)) • u x) ∧
        ∀ x, ‖v x‖ ≤ a x := by
    let f : K → ℂ := fun x ↦ (a x / (a x + b x)) • u x
    have hratio (x : K) : 0 ≤ a x / (a x + b x) ∧ a x / (a x + b x) ≤ 1 := by
      refine ⟨div_nonneg (ha x) (add_nonneg (ha x) (hb x)), ?_⟩
      by_cases hz : a x + b x = 0
      · simp [hz]
      · exact (div_le_one (lt_of_le_of_ne (add_nonneg (ha x) (hb x)) (Ne.symm hz))).mpr
          (le_add_of_nonneg_right (hb x))
    have hf_norm (x : K) : ‖f x‖ ≤ ‖u x‖ := by
      dsimp only [f]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hratio x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hratio x).2
    have hf_cont : Continuous f := by
      rw [continuous_iff_continuousAt]
      intro x
      by_cases hz : a x + b x = 0
      · have huz : u x = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hz] using hu x)
            (norm_nonneg _))
        have hfz : f x = 0 := by simp only [f, huz, smul_zero]
        change Filter.Tendsto f (nhds x) (nhds (f x))
        rw [hfz]
        apply squeeze_zero_norm hf_norm
        simpa only [ContinuousAt, huz, norm_zero] using (u.continuous.continuousAt (x := x)).norm
      · exact (a.continuous.continuousAt.div
          (a.continuous.continuousAt.add b.continuous.continuousAt) hz).smul
          u.continuous.continuousAt
    refine ⟨⟨f, hf_cont⟩, fun _ ↦ rfl, ?_⟩
    intro x
    change ‖f x‖ ≤ a x
    dsimp only [f]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hratio x).1]
    by_cases hz : a x + b x = 0
    · simpa [hz] using ha x
    · calc
        _ ≤ (a x / (a x + b x)) * (a x + b x) :=
          mul_le_mul_of_nonneg_left (hu x) (hratio x).1
        _ = a x := div_mul_cancel₀ _ hz
  have hL_add_upper (a b : C(K, ℝ)) (ha : ∀ x, 0 ≤ a x)
      (hb : ∀ x, 0 ≤ b x) : L (a + b) ≤ L a + L b := by
    apply csSup_le (hA_nonempty _ (fun x ↦ add_nonneg (ha x) (hb x)))
    rintro r ⟨u, hu, rfl⟩
    obtain ⟨v, hv, hva⟩ := hpiece a b ha hb u hu
    obtain ⟨w, hw, hwb⟩ := hpiece b a hb ha u (fun x ↦ by simpa [add_comm] using hu x)
    have hsum : v + w = u := by
      ext x
      change v x + w x = u x
      rw [hv, hw, add_comm (b x) (a x), ← add_smul, ← add_div]
      by_cases hz : a x + b x = 0
      · have huz : u x = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hz] using hu x)
            (norm_nonneg _))
        simp [huz]
      · rw [div_self hz, one_smul]
    calc
      ‖Ψ u‖ = ‖Ψ v + Ψ w‖ := by rw [← map_add, hsum]
      _ ≤ ‖Ψ v‖ + ‖Ψ w‖ := norm_add_le _ _
      _ ≤ L a + L b := add_le_add (le_csSup (hA_bdd _) ⟨v, hva, rfl⟩)
        (le_csSup (hA_bdd _) ⟨w, hwb, rfl⟩)
  have hL_add (a b : C(K, ℝ)) (ha : ∀ x, 0 ≤ a x)
      (hb : ∀ x, 0 ≤ b x) : L (a + b) = L a + L b :=
    le_antisymm (hL_add_upper a b ha hb) (hL_add_lower a b ha hb)
  
  
  let pos (a : C(K, ℝ)) : C(K, ℝ) := ⟨fun x ↦ max (a x) 0, a.continuous.max continuous_const⟩
  have hpos (a : C(K, ℝ)) (x : K) : 0 ≤ pos a x := le_max_right _ _
  have hparts (a : C(K, ℝ)) : pos a - pos (-a) = a := by
    ext x
    change max (a x) 0 - max (-a x) 0 = a x
    rcases le_total 0 (a x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
      ring
  let LR (a : C(K, ℝ)) : ℝ := L (pos a) - L (pos (-a))
  have hLRdiff (v a b : C(K, ℝ)) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
      (hv : a - b = v) : LR v = L a - L b := by
    have he : pos v + b = pos (-v) + a := by
      calc
        pos v + b = (pos v - pos (-v)) + pos (-v) + b := by abel
        _ = v + pos (-v) + b := by rw [hparts]
        _ = pos (-v) + a := by rw [← hv]; abel
    have heL := congrArg L he
    rw [hL_add _ _ (hpos _) hb, hL_add _ _ (hpos _) ha] at heL
    dsimp only [LR]
    linarith
  have hLRnonneg (a : C(K, ℝ)) (ha : ∀ x, 0 ≤ a x) : LR a = L a := by
    simpa only [hL_zero, sub_zero] using hLRdiff a a 0 ha (by simp) (sub_zero a)
  have hLRadd (a b : C(K, ℝ)) : LR (a + b) = LR a + LR b := by
    have he : (pos a + pos b) - (pos (-a) + pos (-b)) = a + b := by
      rw [show (pos a + pos b) - (pos (-a) + pos (-b)) =
        (pos a - pos (-a)) + (pos b - pos (-b)) by abel, hparts, hparts]
    rw [hLRdiff _ _ _ (fun x ↦ add_nonneg (hpos _ x) (hpos _ x))
      (fun x ↦ add_nonneg (hpos _ x) (hpos _ x)) he,
      hL_add _ _ (hpos _) (hpos _), hL_add _ _ (hpos _) (hpos _)]
    dsimp only [LR]
    ring
  have hLRneg (a : C(K, ℝ)) : LR (-a) = -LR a := by
    simp only [LR, neg_neg]
    ring
  have hLRsmul_nonneg (c : ℝ) (hc : 0 ≤ c) (a : C(K, ℝ)) : LR (c • a) = c * LR a := by
    have he : c • pos a - c • pos (-a) = c • a := by rw [← smul_sub, hparts]
    rw [hLRdiff _ _ _ (fun x ↦ mul_nonneg hc (hpos _ x))
      (fun x ↦ mul_nonneg hc (hpos _ x)) he,
      hL_smul _ (hpos _) _ hc, hL_smul _ (hpos _) _ hc]
    dsimp only [LR]
    ring
  have hLRsmul (c : ℝ) (a : C(K, ℝ)) : LR (c • a) = c * LR a := by
    rcases le_total 0 c with hc | hc
    · exact hLRsmul_nonneg c hc a
    · have hneg := hLRsmul_nonneg (-c) (neg_nonneg.mpr hc) a
      rw [neg_smul, hLRneg] at hneg
      linarith
  let realLinear : C(K, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := LR
      map_add' := hLRadd
      map_smul' := hLRsmul }
  let positive : CompactlySupportedContinuousMap K ℝ →ₚ[ℝ] ℝ :=
    PositiveLinearMap.mk₀
      { toFun := fun f ↦ realLinear f.toContinuousMap
        map_add' := fun f g ↦ hLRadd _ _
        map_smul' := fun c f ↦ hLRsmul c _ }
      (fun f hf ↦ by
        change 0 ≤ LR f.toContinuousMap
        rw [hLRnonneg _ hf]
        exact hL_nonneg _ hf)
  let μ₀ : Measure K := RealRMK.rieszMeasure positive
  have hμfinite : IsFiniteMeasure μ₀ := inferInstance
  have hμregular : μ₀.Regular := inferInstance
  have hμintegral (v : C(K, ℝ)) : (∫ x, v x ∂μ₀) = LR v := by
    exact RealRMK.integral_rieszMeasure positive
      (CompactlySupportedContinuousMap.continuousMapEquiv v)
  have hμmass : (μ₀ Set.univ).toReal = L 1 := by
    have he := hμintegral 1
    rw [hLRnonneg _ (by simp)] at he
    simpa [Measure.real] using he
  have hμmass_le : (μ₀ Set.univ).toReal ≤ 1 := by
    rw [hμmass]
    exact (hL_bound 1 (by simp)).trans ((ContinuousMap.norm_le _ zero_le_one).mpr (by simp))
  have hμdominates (u : C(K, ℂ)) : ‖Ψ u‖ ≤ ∫ x, ‖u x‖ ∂μ₀ := by
    have he := hμintegral ⟨fun x ↦ ‖u x‖, u.continuous.norm⟩
    rw [hLRnonneg _ (fun x ↦ norm_nonneg (u x))] at he
    exact he ▸ hL_dominates u
  have hμmass_eq : (μ₀ Set.univ).toReal = 1 := by
    apply le_antisymm hμmass_le
    rw [← hΨ]
    apply Ψ.opNorm_le_bound ENNReal.toReal_nonneg
    intro u
    have hu : Integrable (fun x ↦ ‖u x‖) μ₀ :=
      u.continuous.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc
      ‖Ψ u‖ ≤ ∫ x, ‖u x‖ ∂μ₀ := hμdominates u
      _ ≤ ∫ _, ‖u‖ ∂μ₀ := integral_mono_ae hu (integrable_const _)
          (Filter.Eventually.of_forall u.norm_coe_le_norm)
      _ = (μ₀ Set.univ).toReal * ‖u‖ := by simp [Measure.real, smul_eq_mul]
  let μ : Measure K := ENNReal.ofReal ‖Φ‖ • μ₀
  have hμFinite : IsFiniteMeasure μ :=
    ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ₀ Set.univ)⟩
  have hμRegular : μ.Regular := Measure.Regular.smul ENNReal.ofReal_ne_top
  have hμMass : (μ Set.univ).toReal = ‖Φ‖ := by
    simp [μ, ENNReal.toReal_mul, hμmass_eq]
  
  refine ⟨μ, ?_⟩
  suffices hdensity : ∃ g : K → ℂ, Measurable g ∧ (∀ x, ‖g x‖ ≤ 1) ∧
      ∀ u : C(K, ℂ), Integrable (fun x ↦ u x * g x) μ ∧
        Φ u = ∫ x, u x * g x ∂μ by
    obtain ⟨g, hg, hbound, hrepr⟩ := hdensity
    exact ⟨g, hμFinite, hμRegular, hg, hbound, hμMass, hrepr⟩
  let J : C(K, ℂ) →L[ℂ] Lp ℂ 1 μ₀ := ContinuousMap.toLp 1 μ₀ ℂ
  have hJ (u : C(K, ℂ)) : ‖J u‖ = ∫ x, ‖u x‖ ∂μ₀ := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 1) μ₀ (𝕜 := ℂ) u] with x hx
    rw [hx]
  obtain ⟨T, hT, hTJ⟩ := rudin_dominated_range_hahn_banach
    J.toLinearMap Ψ.toLinearMap (fun u ↦ by change ‖Ψ u‖ ≤ ‖J u‖; rw [hJ]; exact hμdominates u)
  change ∀ u, T (J u) = Ψ u at hTJ
  obtain ⟨g, hg, hbound, hrepr⟩ := rudin_l1_dual_bounded_representative μ₀ T hT
  refine ⟨g, hg, hbound, ?_⟩
  intro u
  have hu : Integrable (fun x ↦ u x) μ₀ :=
    u.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hJu : J u = hu.toL1 u := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp (p := 1) μ₀ (𝕜 := ℂ) u).trans hu.coeFn_toL1.symm
  have hΨu : Ψ u = ∫ x, u x * g x ∂μ₀ := by
    rw [← hTJ u, hJu]
    exact (hrepr u hu).2
  refine ⟨(hrepr u hu).1.smul_measure ENNReal.ofReal_ne_top, ?_⟩
  change Φ u = ∫ x, u x * g x ∂(ENNReal.ofReal ‖Φ‖ • μ₀)
  rw [integral_smul_measure, ENNReal.toReal_ofReal (norm_nonneg _), ← hΨu]
  simp [Ψ, hc.ne']

end HolomorphicAnosov

