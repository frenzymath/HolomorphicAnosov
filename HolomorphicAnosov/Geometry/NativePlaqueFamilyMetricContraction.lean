import HolomorphicAnosov.Geometry.NativePlaqueFamilyCoordinateJet
import HolomorphicAnosov.Geometry.Riemannian.LocalDerivativeDistanceBound
import HolomorphicAnosov.Analysis.InjectiveDerivativeLengthChord
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Tactic

open Set Bundle Manifold MeasureTheory
open scoped ContDiff Manifold Bundle ENNReal NNReal _root_.Topology

namespace HolomorphicAnosov

/-- Strict tensor contraction on the tangent distribution makes sufficiently small members of a
native finite-C1 plaque family nonexpanding for the ambient Riemannian distance of that tensor.
The center neighborhood and parameter radius can be chosen uniformly. (HPS, pp.61–63; Shub, Thm
6.2, pp.71–72) -/
theorem NativePlaqueFamily.local_riemannian_contraction
    {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [RegularSpace M]
    [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)} {x : M}
    (Φ : NativePlaqueFamily 𝓘(ℝ, E) (V := V) D x)
    (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hcontract : ∀ z (v : TangentSpace 𝓘(ℝ, E) z), v ∈ D z →
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g z v‖ ≤ θ * ‖v‖) :
    ∃ N : Set Φ.centerDomain, IsOpen N ∧ ⟨x, Φ.center_mem⟩ ∈ N ∧
      ∃ r : ℝ, 0 < r ∧ r < Φ.radius ∧
        ∀ p ∈ N, ∀ v ∈ Metric.ball (0 : V) r,
          riemannianEDist 𝓘(ℝ, E) (g ((Φ.plaque p).param v)) (g p.val) ≤
            riemannianEDist 𝓘(ℝ, E) ((Φ.plaque p).param v) p.val := by
  have hnear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), θ * (1 + t)^2 * (1 + t) + t < 1 := by
    have hc : Continuous (fun t : ℝ ↦ θ * (1 + t)^2 * (1 + t) + t) := by fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by simpa using hθ1))
  obtain ⟨ε, hε, hε1, hsmall⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      θ * (1 + ε)^2 * (1 + ε) < 1 - ε := by
    have hlim : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t ∧ t < 1 ∧
        θ * (1 + t)^2 * (1 + t) + t < 1 :=
      Filter.Eventually.and self_mem_nhdsWithin
        ((Filter.Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)).and
          (Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear))
    obtain ⟨t, ht, ht1, hts⟩ := hlim.exists
    exact ⟨t, ht, ht1, by linarith⟩
  let a := 1 + ε
  have ha : 1 < a := by dsimp [a]; linarith
  let p₀ : Φ.centerDomain := ⟨x, Φ.center_mem⟩
  let e := extChartAt 𝓘(ℝ, E) x
  let T := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x
  let A := T.symmL ℝ x
  obtain ⟨W, hW, hxW, hWsrc, hchord⟩ := frozen_chart_chord_le_local_riemannianEDist (E := E) x ha
  have hupper := eventually_norm_symmL_trivializationAt_comp_self_lt
    E (TangentSpace 𝓘(ℝ, E)) x ha
  have hvalues : ∀ᶠ z : Φ.centerDomain × V in 𝓝 (p₀, 0),
      (Φ.plaque z.1).param z.2 ∈ W ∧
        ‖(T.symmL ℝ ((Φ.plaque z.1).param z.2)).comp (T.continuousLinearMapAt ℝ x)‖ < a := by
    have hc := Φ.continuousAt_centered_param
    have heq : (Φ.plaque p₀).param 0 = x := (Φ.plaque p₀).centered
    have ht := hc.tendsto
    rw [heq] at ht
    exact ht.eventually (Filter.inter_mem (hW.mem_nhds hxW) hupper)
  obtain ⟨N₀, hN₀, B₀, hB₀, hprod⟩ := mem_nhds_prod_iff.mp hvalues
  obtain ⟨N, hNN₀, hN, hpN⟩ := mem_nhds_iff.mp hN₀
  obtain ⟨b, hb, hbB⟩ := Metric.mem_nhds_iff.mp hB₀
  let r₀ := min b Φ.radius / 2
  have hr₀ : 0 < r₀ := half_pos (lt_min hb Φ.radius_pos)
  have hr₀b : r₀ < b := (half_lt_self (lt_min hb Φ.radius_pos)).trans_le (min_le_left _ _)
  have hr₀R : r₀ < Φ.radius := (half_lt_self (lt_min hb Φ.radius_pos)).trans_le (min_le_right _ _)
  have hcontrol (p : N) (v : V) (hv : v ∈ Metric.ball (0 : V) r₀) :
      (Φ.plaque p.val).param v ∈ W ∧
        ‖(T.symmL ℝ ((Φ.plaque p.val).param v)).comp (T.continuousLinearMapAt ℝ x)‖ < a :=
    hprod (a := (p.val, v)) ⟨hNN₀ p.property, hbB ((Metric.ball_subset_ball hr₀b.le) hv)⟩
  let F : N → V → TangentSpace 𝓘(ℝ, E) x := fun p v ↦ A (e ((Φ.plaque p.val).param v))
  let DF : N × V → V →L[ℝ] TangentSpace 𝓘(ℝ, E) x := fun q ↦
    A.comp (fderiv ℝ (fun v ↦ e ((Φ.plaque q.1.val).param v)) q.2)
  have hFder (p : N) (v : V) (hv : v ∈ Metric.ball (0 : V) r₀) :
      HasFDerivAt (F p) (DF (p, v)) v := by
    have hpv : v ∈ (Φ.plaque p.val).domain := by
      rw [Φ.domain_eq]
      exact (Metric.ball_subset_ball hr₀R.le) hv
    have hφ := ((Φ.plaque p.val).smooth v hpv).contMDiffAt
      ((Φ.plaque p.val).domain_open.mem_nhds hpv)
    have he := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (x := x)
      (by simpa only [extChartAt_source] using hWsrc (hcontrol p v hv).1)
    have hdiff : DifferentiableAt ℝ (fun v ↦ e ((Φ.plaque p.val).param v)) v :=
      (contMDiffAt_iff_contDiffAt.mp (he.comp v hφ)).differentiableAt (by simp)
    exact A.hasFDerivAt.comp v hdiff.hasFDerivAt
  have hDF : ContinuousAt DF ((⟨p₀, hpN⟩ : N), 0) := by
    have hc : ContinuousAt (fun q : N × V ↦
        fderiv ℝ (fun v ↦ e ((Φ.plaque q.1.val).param v)) q.2)
        ((⟨p₀, hpN⟩ : N), 0) :=
      Φ.continuousAt_centered_coordinate_derivative.comp
        (x := ((⟨p₀, hpN⟩ : N), (0 : V))) (f := fun q : N × V ↦ (q.1.val, q.2))
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousAt
    exact continuousAt_const.clm_comp hc
  have hDFinj : Function.Injective (DF ((⟨p₀, hpN⟩ : N), 0)) := by
    have hbase : x ∈ T.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    have hA : Function.Injective A := by
      have heq : A = ((T.continuousLinearEquivAt ℝ x hbase).symm : E →L[ℝ] TangentSpace 𝓘(ℝ, E) x) := by
        exact (T.symm_continuousLinearEquivAt_eq' hbase).symm
      rw [heq]
      exact (T.continuousLinearEquivAt ℝ x hbase).symm.injective
    apply hA.comp
    have h0 : (0 : V) ∈ (Φ.plaque p₀).domain := (Φ.plaque p₀).zero_mem
    have hφ := ((Φ.plaque p₀).smooth 0 h0).contMDiffAt ((Φ.plaque p₀).domain_open.mem_nhds h0)
    have he : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e ((Φ.plaque p₀).param 0) := by
      rw [(Φ.plaque p₀).centered]
      exact mdifferentiableAt_extChartAt (by simp [p₀])
    have hd := mfderiv_comp 0 he (hφ.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hd
    change fderiv ℝ (fun v ↦ e ((Φ.plaque p₀).param v)) 0 = _ at hd
    rw [hd]
    apply Function.Injective.comp _ ((Φ.plaque p₀).immersed 0 h0)
    rw [(Φ.plaque p₀).centered]
    change Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x) x)
    rw [mfderiv_extChartAt_self]
    exact Function.injective_id
  obtain ⟨N₁, hN₁, hpN₁, r, hr, hrr₀, hsegment⟩ :=
    Analysis.parametric_injective_derivative_segment_chord_bound F DF (⟨p₀, hpN⟩ : N)
      hr₀ hε hε1 hFder hDF hDFinj
  let K := θ * a * (1 + ε) / (1 - ε)
  have hK : 0 ≤ K := le_of_lt (div_pos (mul_pos (mul_pos hθ (by linarith)) (by linarith)) (by linarith))
  have hKa : K * a ≤ 1 := by
    dsimp only [K]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - ε)).mpr
    dsimp only [a]
    nlinarith
  refine ⟨Subtype.val '' N₁, hN.isOpenMap_subtype_val _ hN₁,
    ⟨⟨p₀, hpN⟩, hpN₁, rfl⟩, r, hr, hrr₀.trans hr₀R, ?_⟩
  rintro _ ⟨p, hp, rfl⟩ v hv
  let φ := (Φ.plaque p.val).param
  have hv₀ : v ∈ Metric.ball (0 : V) r₀ := (Metric.ball_subset_ball hrr₀.le) hv
  have hzero : (0 : V) ∈ Metric.ball (0 : V) r := Metric.mem_ball_self hr
  have hzero₀ : (0 : V) ∈ Metric.ball (0 : V) r₀ := Metric.mem_ball_self hr₀
  have hdom (w : V) (hw : w ∈ Metric.ball (0 : V) r) : w ∈ (Φ.plaque p.val).domain := by
    rw [Φ.domain_eq]
    exact (Metric.ball_subset_ball (hrr₀.trans hr₀R).le) hw
  have hφ : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ φ (Metric.ball (0 : V) r) :=
    (Φ.plaque p.val).smooth.mono hdom
  have hbase : x ∈ T.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hspeed (w : V) (hw : w ∈ Metric.ball (0 : V) r) :
      ‖mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (g ∘ φ) w v‖ ≤ K * ‖F p v - F p 0‖ := by
    have hw₀ : w ∈ Metric.ball (0 : V) r₀ := (Metric.ball_subset_ball hrr₀.le) hw
    have hwsrc : φ w ∈ (chartAt E x).source := by
      simpa only [extChartAt_source] using hWsrc (hcontrol p w hw₀).1
    have hwbase : φ w ∈ T.baseSet := hwsrc
    have hφdiff := ((hφ w hw).contMDiffAt (Metric.isOpen_ball.mem_nhds hw)).mdifferentiableAt (by simp)
    have hd := mfderiv_comp w (mdifferentiableAt_extChartAt hwsrc) hφdiff
    rw [mfderiv_eq_fderiv] at hd
    have hDf : DF (p, w) v = A (T.continuousLinearMapAt ℝ (φ w)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) φ w v)) := by
      dsimp only [DF]
      rw [TangentBundle.continuousLinearMapAt_trivializationAt hwsrc]
      change A (fderiv ℝ (e ∘ φ) w v) = _
      rw [hd]
      rfl
    have hu : ‖mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) φ w v‖ ≤ a * ‖DF (p, w) v‖ := by
      rw [hDf]
      calc
        _ = ‖((T.symmL ℝ (φ w)).comp (T.continuousLinearMapAt ℝ x))
            (A (T.continuousLinearMapAt ℝ (φ w) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) φ w v)))‖ := by
          rw [ContinuousLinearMap.comp_apply, T.continuousLinearMapAt_symmL hbase,
            T.symmL_continuousLinearMapAt hwbase]
        _ ≤ ‖(T.symmL ℝ (φ w)).comp (T.continuousLinearMapAt ℝ x)‖ * _ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ a * _ := mul_le_mul_of_nonneg_right (hcontrol p w hw₀).2.le (norm_nonneg _)
    have hseg := hsegment p hp v hv 0 hzero w hw
    simp only [sub_zero] at hseg
    have hb : ‖DF (p, w) v‖ ≤ (1 + ε) / (1 - ε) * ‖F p v - F p 0‖ := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (by linarith : 0 < 1 - ε)).mpr
      nlinarith
    have htangent : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) φ w v ∈ D (φ w) := by
      rw [← (Φ.plaque p.val).tangent w (hdom w hw)]
      exact ⟨v, rfl⟩
    rw [mfderiv_comp w (g.contMDiff.mdifferentiableAt (by simp)) hφdiff]
    change ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g (φ w)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) φ w v)‖ ≤ _
    calc
      _ ≤ θ * ‖mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) φ w v‖ := hcontract _ _ htangent
      _ ≤ θ * (a * ‖DF (p, w) v‖) := mul_le_mul_of_nonneg_left hu hθ.le
      _ ≤ θ * (a * ((1 + ε) / (1 - ε) * ‖F p v - F p 0‖)) := by gcongr
      _ = K * ‖F p v - F p 0‖ := by dsimp [K]; ring
  let η := AffineMap.lineMap (k := ℝ) (0 : V) v
  have hη : ContMDiff 𝓘(ℝ) 𝓘(ℝ, V) ∞ η :=
    contMDiff_iff_contDiff.mpr (AffineMap.contDiff_lineMap _ _)
  have hηmem : MapsTo η (Icc (0 : ℝ) 1) (Metric.ball (0 : V) r) :=
    (convex_ball (0 : V) r).mapsTo_lineMap hzero hv
  let ψ := g ∘ φ
  have hψ : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ ψ (Metric.ball (0 : V) r) :=
    g.contMDiff.comp_contMDiffOn hφ
  have himage : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ (ψ ∘ η) (Icc 0 1) :=
    hψ.comp hη.contMDiffOn hηmem
  have hlength : pathELength 𝓘(ℝ, E) (ψ ∘ η) 0 1 ≤
      ENNReal.ofReal K * ‖F p v - F p 0‖ₑ := by
    rw [pathELength_eq_lintegral_mfderivWithin_Icc]
    calc
      _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal K * ‖F p v - F p 0‖ₑ := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        have hdη : mfderivWithin 𝓘(ℝ) 𝓘(ℝ, V) η (Icc 0 1) t (1 : ℝ) = v := by
          rw [mfderivWithin_eq_fderivWithin]
          rw [(AffineMap.hasDerivWithinAt_lineMap (a := (0 : V)) (b := v)).hasFDerivWithinAt.fderivWithin
            (uniqueDiffOn_Icc zero_lt_one t ht)]
          change (1 : ℝ) • (v - 0) = v
          simp
        have hchain := mfderiv_comp_mfderivWithin t
          (((hψ (η t) (hηmem ht)).contMDiffAt (Metric.isOpen_ball.mem_nhds (hηmem ht))).mdifferentiableAt (by simp))
          (hη.contMDiffOn.mdifferentiableOn (by simp) t ht)
          ((uniqueDiffOn_Icc zero_lt_one t ht).uniqueMDiffWithinAt)
        rw [hchain]
        change ‖mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ψ (η t)
          (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, V) η (Icc 0 1) t 1)‖ₑ ≤ _
        have hvel : (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ψ (η t))
            (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, V) η (Icc 0 1) t 1) =
              mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ψ (η t) v := congrArg
          (fun w : V ↦ mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ψ (η t) w) hdη
        rw [hvel, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hK]
        exact ENNReal.ofReal_le_ofReal (hspeed (η t) (hηmem ht))
      _ = _ := by simp
  have hend : riemannianEDist 𝓘(ℝ, E) (g (φ v)) (g p.val.val) ≤ pathELength 𝓘(ℝ, E) (ψ ∘ η) 0 1 := by
    rw [riemannianEDist_comm]
    apply riemannianEDist_le_pathELength (himage.of_le (by simp)) _ _ zero_le_one
    · simp [ψ, η, φ, (Φ.plaque p.val).centered]
    · simp [ψ, η]
  have hc : ‖F p v - F p 0‖ₑ ≤ ENNReal.ofReal a * riemannianEDist 𝓘(ℝ, E) (φ v) p.val.val := by
    have hh := hchord (φ v) (hcontrol p v hv₀).1 (φ 0) (hcontrol p 0 hzero₀).1
    simpa only [F, ← map_sub, φ, (Φ.plaque p.val).centered] using hh
  apply hend.trans (hlength.trans _)
  calc
    ENNReal.ofReal K * ‖F p v - F p 0‖ₑ ≤
        ENNReal.ofReal K * (ENNReal.ofReal a * riemannianEDist 𝓘(ℝ, E) (φ v) p.val.val) := by gcongr
    _ = ENNReal.ofReal (K * a) * riemannianEDist 𝓘(ℝ, E) (φ v) p.val.val := by
      rw [ENNReal.ofReal_mul hK, mul_assoc]
    _ ≤ riemannianEDist 𝓘(ℝ, E) (φ v) p.val.val := by
      have hk : ENNReal.ofReal (K * a) ≤ 1 := by exact_mod_cast ENNReal.ofReal_le_ofReal hKa
      simpa only [one_mul] using mul_le_mul hk le_rfl zero_le zero_le


end HolomorphicAnosov
