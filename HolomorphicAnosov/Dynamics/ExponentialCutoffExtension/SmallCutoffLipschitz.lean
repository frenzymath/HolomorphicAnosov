import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.UniformFrameDerivativeBound
import HolomorphicAnosov.Dynamics.CutoffProductLipschitz
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.SquaredNormCutoffDerivativeBound

noncomputable section
namespace HolomorphicAnosov.ExponentialCutoff
open Bundle Set ExponentialLift
open scoped Manifold ContDiff Topology _root_.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- The concrete metric cutoff of a compact family tangent to Tf has an
arbitrarily small global remainder in the prescribed continuous fibre norm.

Source: HPS (1977), proof of Theorem 5.5, pp. 61–62; Lee (2003), Lemma 11.19
and Theorem 17.19, pp. 278 and 457–458; Merry, Lecture 32, Theorem 32.2,
equations (32.6)–(32.7). This is the quantitative part of the compact-family
cutoff construction, without the separate higher-jet continuity assertion.

Compare the prescribed norm ν with the original metric norm by positive
constants m and M₀. Choose a global bump derivative bound K and set
η = εm / (M₀(1+2K)). Apply exists_uniform_frame_derivative_bound to the metric
norm itself and this η. Conjugation by the actual source and receiving tangent
frame equivalences identifies its derivative differences with D H_p - Tf_p;
the equality at zero follows from the supplied tangency certificate. In each
fixed fibre the radial cutoff is differentiable, bounded by one, vanishes for
metric norm at least δ, and has derivative norm at most 2K/δ. Its last estimate
is obtained by testing every direction with the squared-norm line derivative
bound. The remainder q=H-Tf vanishes at zero and has derivative bounded by η on
the closed cutoff disc. The cutoff_product_lipschitz theorem gives the metric
all-pairs bound (1+2K)η. Both branches of the concrete extension equal Tf+χq,
since χ vanishes outside the smaller cutoff disc. Finally the two norm
comparisons give the ν bound with constant M₀(1+2K)η/m=ε. All off-domain
values of H remain unrestricted, and empty bases are vacuous. -/
theorem exists_small_cutoff_lipschitz
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (hA : IsCompact A) (f : M → M) (r : ℕ∞)
    (hr : 1 ≤ r) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) r f)
    (hfA : MapsTo f A A)
    (ν : ContinuousRestrictedTangentNorm (E := E) A)
    (H : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    {R : ℝ} (hR : 0 < R)
    (hzero : ∀ p : A, H p 0 = 0 ∧ HasFDerivAt
      (fun u : E ↦ tangentSpaceCastModel 𝓘(ℝ, E) (f p)
        (H p ((tangentSpaceCastModel 𝓘(ℝ, E) (p : M)).symm u)))
      (modelDerivative f p) 0)
    (hjets : HasContinuousVerticalJetsOn A f r H
      (fun p ↦ {v | metricNorm g p v < R}))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧
      ∀ (p : A) (v w : TangentSpace 𝓘(ℝ, E) (p : M)),
        ν.value ⟨f p, hfA p.property⟩
          ((extension A f g H R δ p v - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v) -
            (extension A f g H R δ p w - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) w)) ≤
          ε * ν.value p (v - w) := by
  classical
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.toContinuousRiemannianMetric.toRiemannianMetric⟩
  let νg : ContinuousRestrictedTangentNorm (E := E) A :=
    { value := fun _ v ↦ ‖v‖
      nonneg := fun _ v ↦ norm_nonneg v
      eq_zero_iff := fun _ v ↦ norm_eq_zero
      add_le := fun _ v w ↦ norm_add_le v w
      smul := fun _ a v ↦ by simpa only [Real.norm_eq_abs] using norm_smul a v
      continuous := (ExponentialLift.continuous_metricNorm g).comp continuous_subtype_val }
  by_cases hEmpty : A = ∅
  · refine ⟨R / 2, by positivity, by linarith, ?_⟩
    intro p
    exact (Set.notMem_empty p.val (hEmpty ▸ p.property)).elim
  obtain ⟨K, hK, hKbound⟩ := scalarBump_derivative_bound
  obtain ⟨m, M₀, hm, hM₀, hlower, hupper⟩ :=
    finite_core_two_sided_norm_comparison_from_canonical g A hA ν
  let η : ℝ := ε * m / (M₀ * (1 + 2 * K))
  have hfactor : 0 < M₀ * (1 + 2 * K) := by positivity
  have hη : 0 < η := div_pos (mul_pos hε hm) hfactor
  have hcutoff : ∀ (δ : ℝ), 0 < δ → ∀ (p : M)
      (v w : TangentSpace 𝓘(ℝ, E) p),
      |deriv (fun t : ℝ ↦ fibreCutoff g δ p (v + t • w)) 0| ≤
        (2 * K / δ) * metricNorm g p w := by
    intro δ hδ p v w
    let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
      ⟨g.toContinuousRiemannianMetric.toRiemannianMetric⟩
    have h := squared_norm_cutoff_derivative_bound scalarBump
      ((scalarBump.contDiff : ContDiff ℝ ∞ scalarBump).differentiable (by simp))
      hδ hK hKbound (fun t ht ↦ scalarBump_derivative_zero ht) v w
    change |deriv (fun t : ℝ ↦ scalarBump
      (inner ℝ (v + t • w) (v + t • w) / δ ^ 2)) 0| ≤ (2 * K / δ) * ‖w‖
    simpa only [real_inner_self_eq_norm_sq] using h
  have hηbound : M₀ * ((1 + 2 * K) * η) = ε * m := by
    dsimp [η]
    field_simp
  obtain ⟨δ, hδ, hδR, huniform⟩ := exists_uniform_frame_derivative_bound
    g A hA f hf.continuous hfA νg H r hr hR hjets hη
  have hHDiff (p : A) (v : TangentSpace 𝓘(ℝ, E) (p : M))
      (hv : metricNorm g p v < R) : DifferentiableAt ℝ (H p) v := by
    let J := tangentSpaceCastModel 𝓘(ℝ, E) (p : M)
    let L := tangentSpaceCastModel 𝓘(ℝ, E) (f p)
    have hopen : IsOpen {u : E | metricNorm g p (J.symm u) < R} := by
      change IsOpen {u : E | ‖J.symm u‖ < R}
      exact isOpen_lt (continuous_norm.comp J.symm.continuous) continuous_const
    have hmem : {u : E | metricNorm g p (J.symm u) < R} ∈ 𝓝 (J v) :=
      hopen.mem_nhds (by simpa only [Set.mem_ofPred_eq, J.symm_apply_apply] using hv)
    have hd := ((hjets.1 p).contDiffAt hmem).differentiableAt (by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ∞) < 1) hr)))
    have hc := L.symm.differentiableAt.comp v (hd.comp v J.differentiableAt)
    convert hc using 1
    ext w
    simp [Function.comp_def, J, L]
  have hHderivZero (p : A) : fderiv ℝ (H p) 0 = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) := by
    let J := tangentSpaceCastModel 𝓘(ℝ, E) (p : M)
    let L := tangentSpaceCastModel 𝓘(ℝ, E) (f p)
    have hc := L.symm.hasFDerivAt.comp 0 (((hzero p).2).comp 0 J.hasFDerivAt)
    have hd : HasFDerivAt (H p) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M)) 0 := by
      convert hc using 1
      · ext w
        simp [Function.comp_def, J, L]
      · ext w
        simp [modelDerivative, J, L]
    exact hd.fderiv
  have hHsmall (p : A) (v : TangentSpace 𝓘(ℝ, E) (p : M))
      (hv : metricNorm g p v ≤ δ) :
      ‖fderiv ℝ (H p) v - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M)‖ ≤ η := by
    obtain ⟨s, t, hs, ht, hb⟩ := huniform p
    let es := trivializationAt E (TangentSpace 𝓘(ℝ, E)) (s : M)
    let et := trivializationAt E (TangentSpace 𝓘(ℝ, E)) (t : M)
    let J := es.continuousLinearEquivAt ℝ (p : M) hs
    let L := et.continuousLinearEquivAt ℝ (f p) ht
    have hexpr : fibreExpression A f H s t p = L ∘ H p ∘ J.symm := by
      ext u
      change et.continuousLinearMapAt ℝ (f p) (H p (es.symmL ℝ (p : M) u)) =
        L (H p (J.symm u))
      rw [← et.coe_continuousLinearEquivAt_eq (R := ℝ) ht,
        ← es.symm_continuousLinearEquivAt_eq (R := ℝ) hs]
    have hv' : metricNorm g p (es.symmL ℝ (p : M) (J v)) ≤ δ := by
      simpa only [← es.symm_continuousLinearEquivAt_eq (R := ℝ) hs, J,
        ContinuousLinearEquiv.symm_apply_apply] using hv
    apply ContinuousLinearMap.opNorm_le_bound _ hη.le
    intro w
    have hh := hb (J v) hv' (J w)
    change ‖et.symmL ℝ (f p)
      ((fderiv ℝ (fibreExpression A f H s t p) (J v) -
        fderiv ℝ (fibreExpression A f H s t p) 0) (J w))‖ ≤
      η * ‖es.symmL ℝ (p : M) (J w)‖ at hh
    rw [hexpr] at hh
    simp only [← Function.comp_assoc, L.comp_fderiv, J.symm.comp_right_fderiv,
      map_zero, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, J.symm_apply_apply] at hh
    rw [← et.symm_continuousLinearEquivAt_eq (R := ℝ) ht,
      ← es.symm_continuousLinearEquivAt_eq (R := ℝ) hs] at hh
    simpa only [← map_sub, L, J, ContinuousLinearEquiv.symm_apply_apply, hHderivZero p,
      sub_apply] using hh
  have hLipschitz (p : A) (v w : TangentSpace 𝓘(ℝ, E) (p : M)) :
      ν.value ⟨f p, hfA p.property⟩
        ((extension A f g H R δ p v - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v) -
          (extension A f g H R δ p w - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) w)) ≤
      ε * ν.value p (v - w) := by
    let χ := fibreCutoff g δ (p : M)
    let q := fun v : TangentSpace 𝓘(ℝ, E) (p : M) ↦
      H p v - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v
    have hχ : Differentiable ℝ χ := by
      have hc : ContDiff ℝ ∞ χ := by
        dsimp [χ, fibreCutoff]
        apply scalarBump.contDiff.comp
        fun_prop
      exact hc.differentiable (by simp)
    have hχbound (x) : ‖χ x‖ ≤ 1 := by
      dsimp [χ, fibreCutoff]
      rw [abs_of_nonneg scalarBump.nonneg]
      exact scalarBump.le_one
    have hχderiv (x : TangentSpace 𝓘(ℝ, E) (p : M)) (_hx : ‖x‖ ≤ δ) :
        ‖fderiv ℝ χ x‖ ≤ (2 * K) / δ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro u
      have hline : HasDerivAt (fun t : ℝ ↦ x + t • u) u 0 := by
        convert! ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add x using 1; simp
      have hcx : HasFDerivAt χ (fderiv ℝ χ x) (x + (0 : ℝ) • u) := by
        simpa only [zero_smul, add_zero] using (hχ x).hasFDerivAt
      have hc := hcx.comp_hasDerivAt 0 hline
      have hc' : HasDerivAt (fun t : ℝ ↦ χ (x + t • u)) ((fderiv ℝ χ x) u) 0 := by
        convert! hc using 1
      have hb := hcutoff δ hδ (p : M) x u
      rw [hc'.deriv] at hb
      exact hb
    have hχzero (x : TangentSpace 𝓘(ℝ, E) (p : M)) (hx : δ < ‖x‖) : χ x = 0 :=
      fibreCutoff_zero g hδ (p : M) x hx.le
    have hqzero : q 0 = 0 := by simp [q, (hzero p).1]
    have hq (x : TangentSpace 𝓘(ℝ, E) (p : M)) (hx : ‖x‖ ≤ δ) :
        DifferentiableAt ℝ q x :=
      (hHDiff p x (lt_of_le_of_lt hx hδR)).sub
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M)).differentiableAt
    have hqderiv (x : TangentSpace 𝓘(ℝ, E) (p : M)) (hx : ‖x‖ ≤ δ) :
        ‖fderiv ℝ q x‖ ≤ η := by
      have hd := (hHDiff p x (lt_of_le_of_lt hx hδR)).hasFDerivAt.sub
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M)).hasFDerivAt
      change HasFDerivAt q (fderiv ℝ (H p) x - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M)) x at hd
      rw [hd.fderiv]
      exact hHsmall p x hx
    have hmetric := cutoff_product_lipschitz χ q hδ (mul_nonneg (by norm_num) hK)
      hη.le hχ hχbound hχderiv hχzero hqzero hq hqderiv v w
    have hformula (x : TangentSpace 𝓘(ℝ, E) (p : M)) :
        extension A f g H R δ p x - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) x =
          χ x • q x := by
      by_cases hx : metricNorm g p x < R
      · simp [extension, hx, χ, q]
      · have hxd : δ < metricNorm g p x := lt_of_lt_of_le hδR (le_of_not_gt hx)
        simp [extension, hx, χ, fibreCutoff_zero g hδ (p : M) x hxd.le]
    rw [hformula v, hformula w]
    calc
      ν.value ⟨f p, hfA p.property⟩ (χ v • q v - χ w • q w) ≤
          M₀ * ‖χ v • q v - χ w • q w‖ := hupper _ _
      _ ≤ M₀ * ((1 + 2 * K) * η * ‖v - w‖) :=
        mul_le_mul_of_nonneg_left hmetric hM₀.le
      _ = ε * (m * ‖v - w‖) := by rw [← mul_assoc, hηbound]; ring
      _ ≤ ε * ν.value p (v - w) := mul_le_mul_of_nonneg_left (hlower p _) hε.le
  exact ⟨δ, hδ, hδR, hLipschitz⟩

end HolomorphicAnosov.ExponentialCutoff
