import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Basic
import HolomorphicAnosov.Ghys.CurveJetAffineData
import HolomorphicAnosov.Ghys.NativeLeafwiseParametrizationJetBundle

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter Bundle Manifold TopologicalSpace
open scoped ContDiff Manifold Bundle _root_.Topology ENNReal
universe u

/-- Under the stated compact-uniform approximation hypotheses, the invariant jet section is holomorphic along each leaf. (Ghys, Lemma 3.3) -/
theorem invariant_jet_leafwise_holomorphic_of_approximation {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
    [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)] [∀ i, T2Space (L i)]
    [∀ i, SecondCountableTopology (L i)]
    (s : NativeLeafwiseJet1 L → NativeLeafwiseJet2 L)
    (hs : ∀ j, nativeLeafwiseJetTruncation L (s j) = j)
    (hscale : ∀ (omega : ℂˣ) j, s (nativeLeafwiseJet1Scale L omega j) =
      nativeLeafwiseJet2Reparametrize L (.scale omega) (s j))
    (happrox : ∀ i (τ : CurveJet1 (L i) → CurveJet2 (L i)),
      (∀ j, s (nativeLeafwiseJet1Inclusion L i j) = nativeLeafwiseJet2Inclusion L i (τ j)) →
      ∀ (c : LeafChart (L i)) (A : ℂ → ℂ),
      (∀ j, curveJet1Base (L i) j ∈ c.1.source →
        (curveJet2Coeff (L i) c (τ j)).2 =
          A (curveJet1Coeff (L i) c j).1 * (curveJet1Coeff (L i) c j).2 ^ 2) →
      ∀ z ∈ c.1.target, ∃ (V : Set ℂ) (F : ℕ → ℂ → ℂ) (rho : ℂ → ℝ) (C q : ℝ),
        IsOpen V ∧ z ∈ V ∧ V ⊆ c.1.target ∧ ContinuousOn rho V ∧
        0 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧
        (∀ᶠ n in atTop, DifferentiableOn ℂ (F n) V) ∧
        (∀ᶠ n in atTop, ∀ z ∈ V, ‖F n z - A z‖ ≤ C * q ^ n * rho z)) :
    letI : ∀ i, ChartedSpace (ℂ × ℂ) (CurveJet1 (L i)) := nativeLeafJet1Charts L
    letI : ∀ i, ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 (L i)) := nativeLeafJet2Charts L
    ∀ i, ∃ τ : CurveJet1 (L i) → CurveJet2 (L i),
      (∀ j, s (nativeLeafwiseJet1Inclusion L i j) = nativeLeafwiseJet2Inclusion L i (τ j)) ∧
      ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ τ := by
  have scalarLimit {V : Set ℂ} (hV : IsOpen V) (A : ℂ → ℂ) (F : ℕ → ℂ → ℂ)
      (rho : ℂ → ℝ) (hrho : ContinuousOn rho V)
      (C q : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q < 1)
      (hhol : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) V)
      (hbound : ∀ᶠ n in atTop, ∀ z ∈ V, ‖F n z - A z‖ ≤ C * q ^ n * rho z) :
      DifferentiableOn ℂ A V := by
    apply TendstoLocallyUniformlyOn.differentiableOn (F := F) ?_ hhol hV
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hV).mpr
    intro K hKV hK
    obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (hrho.mono hKV)
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have hlim : Tendsto (fun n : ℕ ↦ C * q ^ n * R) atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).const_mul C).mul_const R
    filter_upwards [hbound, hlim.eventually_lt_const hε] with n hn hsmall z hz
    rw [dist_comm, dist_eq_norm]
    exact (hn z (hKV hz)).trans_lt ((mul_le_mul_of_nonneg_left
      ((le_abs_self (rho z)).trans (by simpa only [Real.norm_eq_abs] using hR z hz))
      (mul_nonneg hC (pow_nonneg hq n))).trans_lt hsmall)
  have graphHolomorphic (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]
      [IsManifold 𝓘(ℂ) ∞ L] [T2Space L] [SecondCountableTopology L]
      (A1 : ChartedSpace (ℂ × ℂ) (CurveJet1 L))
      (A2 : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L))
      (hAtlases : CurveJetCoefficientAtlases L A1 A2)
      (s : CurveJet1 L → CurveJet2 L)
      (htrunc : ∀ j, curveJetTruncation L (s j) = j)
      (hcoeff : ∀ c : LeafChart L, ∃ A : ℂ → ℂ,
        DifferentiableOn ℂ A c.1.target ∧
        ∀ j, curveJet1Base L j ∈ c.1.source →
          (curveJet2Coeff L c (s j)).2 =
            A (curveJet1Coeff L c j).1 * (curveJet1Coeff L c j).2 ^ 2) :
      letI := A1
      letI := A2
      ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ s := by
    let := A1
    let := A2
    intro j
    let c : LeafChart L := ⟨chartAt ℂ (curveJet1Base L j),
      IsManifold.chart_mem_maximalAtlas _⟩
    have hjc : curveJet1Base L j ∈ c.1.source := mem_chart_source _ _
    obtain ⟨A, hA, hquad⟩ := hcoeff c
    obtain ⟨e1, e2, _, _, hs1, hs2, ht1, ht2, he1, he2,
      he1smooth, _, _, he2inv⟩ := hAtlases.2.2.1 c
    have hsbase (k : CurveJet1 L) : curveJet2Base L (s k) = curveJet1Base L k := by
      rw [← curve_jet_truncation_base L (s k), htrunc]
    have hj1 : j ∈ e1.source := by rwa [hs1]
    have htarget (k : CurveJet1 L) (hk : k ∈ e1.source) :
        (e1 k, A (e1 k).1 * (e1 k).2 ^ 2) ∈ e2.target := by
      rw [ht2]
      have h := e1.map_source hk
      rwa [ht1] at h
    have heq : s =ᶠ[𝓝 j] (fun k ↦ e2.symm (e1 k, A (e1 k).1 * (e1 k).2 ^ 2)) := by
      filter_upwards [e1.open_source.mem_nhds hj1] with k hk
      have hkc : curveJet1Base L k ∈ c.1.source := by rwa [hs1] at hk
      have hsk : s k ∈ e2.source := by
        rw [hs2]
        change curveJet2Base L (s k) ∈ c.1.source
        rw [hsbase]
        exact hkc
      have hfirst := ((leaf_jet_complex_manifold L).2.2.2.1 c).2.2 (s k) (hsbase k ▸ hkc)
      have hcoord : e2 (s k) = (e1 k, A (e1 k).1 * (e1 k).2 ^ 2) := by
        rw [he2 hsk, he1 hk]
        apply Prod.ext
        · simpa only [htrunc] using hfirst.2.symm
        · exact hquad k hkc
      rw [← hcoord, e2.left_inv hsk]
    have h1 := he1smooth.contMDiffAt (e1.open_source.mem_nhds hj1)
    have h2 := he2inv.contMDiffAt (e2.open_target.mem_nhds (htarget j hj1))
    have hjtarget : (e1 j).1 ∈ c.1.target := by
      have h := e1.map_source hj1
      rw [ht1] at h
      exact h.1
    have hscalar : ContDiffAt ℂ ∞ A (e1 j).1 :=
      (hA.contDiffOn c.1.open_target).contDiffAt (c.1.open_target.mem_nhds hjtarget)
    have hgraph : ContDiffAt ℂ ∞
        (fun w : ℂ × ℂ ↦ (w, A w.1 * w.2 ^ 2)) (e1 j) :=
      contDiffAt_id.prodMk ((hscalar.comp _ contDiffAt_fst).mul (contDiffAt_snd.pow 2))
    exact (h2.comp j (hgraph.contMDiffAt.comp j h1)).congr_of_eventuallyEq heq
  have leafRestriction {ι : Type u} (L : ι → Type u)
      [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
      [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
      (s : NativeLeafwiseJet1 L → NativeLeafwiseJet2 L)
      (hs : ∀ j, nativeLeafwiseJetTruncation L (s j) = j) :
      ∀ i, ∃ τ : CurveJet1 (L i) → CurveJet2 (L i),
        (∀ j, s (nativeLeafwiseJet1Inclusion L i j) = nativeLeafwiseJet2Inclusion L i (τ j)) ∧
        ∀ j, curveJetTruncation (L i) (τ j) = j := by
    classical
    intro i
    have hfibre (j : CurveJet1 (L i)) : ∃ w : CurveJet2 (L i), s ⟨i, j⟩ = ⟨i, w⟩ := by
      generalize h : s ⟨i, j⟩ = z
      obtain ⟨k, w⟩ := z
      have hi := congrArg Sigma.fst (hs ⟨i, j⟩)
      rw [h] at hi
      change k = i at hi
      subst k
      exact ⟨w, rfl⟩
    choose τ hτ using hfibre
    refine ⟨τ, hτ, ?_⟩
    intro j
    have h := hs ⟨i, j⟩
    rw [hτ j] at h
    exact eq_of_heq (Sigma.mk.inj h).2
  have coefficientRepresentation (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]
      [IsManifold 𝓘(ℂ) ∞ L] [T2Space L] [SecondCountableTopology L]
      (A1 : ChartedSpace (ℂ × ℂ) (CurveJet1 L))
      (A2 : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L))
      (hAtlases : CurveJetCoefficientAtlases L A1 A2)
      (s : CurveJet1 L → CurveJet2 L)
      (htrunc : ∀ j, curveJetTruncation L (s j) = j)
      (hscale : ∀ (omega : ℂˣ) j,
        s (curveJet1Scale L omega j) = curveJet2Reparametrize L (.scale omega) (s j))
      (c : LeafChart L) :
      ∃ A : ℂ → ℂ, ∀ j, curveJet1Base L j ∈ c.1.source →
        (curveJet2Coeff L c (s j)).2 =
          A (curveJet1Coeff L c j).1 * (curveJet1Coeff L c j).2 ^ 2 := by
    obtain ⟨e1, e2, _, _, hs1, hs2, ht1, ht2, he1, he2, _⟩ := hAtlases.2.2.1 c
    let A := fun z : ℂ ↦ (e2 (s (e1.symm (z, 1)))).2
    have hunit (z : ℂ) (hz : z ∈ c.1.target) : (z, 1) ∈ e1.target := by
      rw [ht1]
      exact ⟨hz, one_ne_zero⟩
    have hsbase (j : CurveJet1 L) : curveJet2Base L (s j) = curveJet1Base L j := by
      rw [← curve_jet_truncation_base L (s j), htrunc]
    have hssource (j : CurveJet1 L) (hj : j ∈ e1.source) : s j ∈ e2.source := by
      rw [hs2]
      change curveJet2Base L (s j) ∈ c.1.source
      rw [hsbase]
      rwa [hs1] at hj
    refine ⟨A, ?_⟩
    intro j hj
    have hbij := ((leaf_jet_complex_manifold L).2.2.2.1 c).1
    let w := curveJet1Coeff L c j
    have hw : w ∈ curveJet1Target L c := hbij.mapsTo hj
    let j₀ := e1.symm (w.1, 1)
    have hj₀ : j₀ ∈ e1.source := e1.map_target (hunit _ hw.1)
    have hj₀base : curveJet1Base L j₀ ∈ c.1.source := by rwa [hs1] at hj₀
    have hj₀coeff : curveJet1Coeff L c j₀ = (w.1, 1) := by
      rw [← he1 hj₀]
      exact e1.right_inv (hunit _ hw.1)
    let omega : ℂˣ := Units.mk0 w.2 hw.2
    have hscale1 := (curve_jet_reparametrization L).2.2.2.1 omega j₀
    have hscaledbase : curveJet1Base L (curveJet1Scale L omega j₀) ∈ c.1.source :=
      hscale1.1.symm ▸ hj₀base
    have hscaled : curveJet1Scale L omega j₀ = j := by
      apply hbij.injOn hscaledbase hj
      rw [hscale1.2 c hj₀base, hj₀coeff]
      simp only [omega, Units.val_mk0, mul_one]
      exact Prod.eta w
    have hquad := (curve_jet_reparametrization L).2.2.1 (.scale omega) (s j₀)
    have hquadcoeff := congrArg Prod.snd (hquad.2.2 c (hsbase j₀ ▸ hj₀base))
    have hA : A w.1 = (curveJet2Coeff L c (s j₀)).2 :=
      congrArg Prod.snd (he2 (hssource j₀ hj₀))
    change (curveJet2Coeff L c (s j)).2 = A w.1 * w.2 ^ 2
    rw [← hscaled, hscale, hquadcoeff, hA]
    simp only [CurveJetReparametrization.scale, omega, Units.val_mk0, mul_zero]
    ring
  have leafScaling {ι : Type u} (L : ι → Type u)
      [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
      [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
      (s : NativeLeafwiseJet1 L → NativeLeafwiseJet2 L)
      (hscale : ∀ (omega : ℂˣ) j, s (nativeLeafwiseJet1Scale L omega j) =
        nativeLeafwiseJet2Reparametrize L (.scale omega) (s j))
      (i : ι) (τ : CurveJet1 (L i) → CurveJet2 (L i))
      (hτ : ∀ j, s (nativeLeafwiseJet1Inclusion L i j) = nativeLeafwiseJet2Inclusion L i (τ j)) :
      ∀ (omega : ℂˣ) j,
        τ (curveJet1Scale (L i) omega j) = curveJet2Reparametrize (L i) (.scale omega) (τ j) := by
    intro omega j
    have h := hscale omega (nativeLeafwiseJet1Inclusion L i j)
    change s (nativeLeafwiseJet1Inclusion L i (curveJet1Scale (L i) omega j)) = _ at h
    rw [hτ, hτ] at h
    exact eq_of_heq (Sigma.mk.inj h).2
  let : ∀ i, ChartedSpace (ℂ × ℂ) (CurveJet1 (L i)) := nativeLeafJet1Charts L
  let : ∀ i, ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 (L i)) := nativeLeafJet2Charts L
  intro i
  obtain ⟨τ, hτ, htrunc⟩ := leafRestriction L s hs i
  have hτscale := leafScaling L s hscale i τ hτ
  have hAtlases : CurveJetCoefficientAtlases (L i)
      (nativeLeafJet1Charts L i) (nativeLeafJet2Charts L i) := by
    obtain ⟨_, _, _, _, h1, h2, _, _, _, _, _, hc, hsource1, hsource2⟩ :=
      (leaf_jet_complex_manifold (L i)).2.2.2.2.choose_spec.choose_spec
    exact ⟨h1, h2, hc, hsource1, hsource2⟩
  refine ⟨τ, hτ, graphHolomorphic (L i) _ _ hAtlases τ htrunc ?_⟩
  intro c
  obtain ⟨A, hA⟩ := coefficientRepresentation (L i) _ _ hAtlases τ htrunc hτscale c
  refine ⟨A, ?_, hA⟩
  intro z hz
  obtain ⟨V, F, rho, C, q, hV, hzV, hVc, hrho, hC, hq, hq1, hhol, hbound⟩ :=
    happrox i τ hτ c A hA z hz
  exact ((scalarLimit hV A F rho hrho C q hC hq hq1 hhol hbound).differentiableAt
    (hV.mem_nhds hzV)).differentiableWithinAt

end HolomorphicAnosov.Ghys

