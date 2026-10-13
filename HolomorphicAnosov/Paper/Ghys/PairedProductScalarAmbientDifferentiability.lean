import HolomorphicAnosov.Analysis.HolomorphicProductDifferentiability
import HolomorphicAnosov.Geometry.Manifold.OpenSubsetInclusionTangentG9
import HolomorphicAnosov.Paper.Ghys.NativeUnstableComplexRankOneFromRealRankTwo
import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Paper.Zhang.Anosov

/-! Ambient complex differentiability of scalar coordinates on native Anosov paired products. (Ghys,
Prop. 2.2 pp.589–590; Demailly, I §3.B–C pp.22–23) -/



namespace HolomorphicAnosov.Ghys

universe u
open scoped Manifold ContDiff _root_.Topology
attribute [local instance] complex_isManifold_real

set_option backward.isDefEq.respectTransparency false in
/-- A continuous scalar coordinate of a native Anosov paired product is ambient complex
differentiable if it is holomorphic on the curve receiving branches and constant on the stable
receiving branches. (Ghys, Prop. 2.2 pp.589–590; Demailly, I §3.B–C pp.22–23) -/
theorem pairedProduct_scalar_ambient_mdifferentiableOn
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X] (_hd : 2 ≤ d)
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution)
    {ιs ιu : Type u} {Ls : ιs → Type u} {Lu : ιu → Type u}
    [∀ i, TopologicalSpace (Ls i)] [∀ i, TopologicalSpace (Lu i)]
    [∀ i, ChartedSpace (Fin (2 * d - 2) → ℝ) (Ls i)]
    [∀ i, ChartedSpace (Fin 2 → ℝ) (Lu i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (2 * d - 2) → ℝ) ∞ (Ls i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (Lu i)]
    (S : HPS.LeafPartition a.splitting.stable.toDistribution ιs Ls (fun _ ↦ 2 * d - 2))
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ιu Lu (fun _ ↦ 2))
    (complexChart : ∀ i, ChartedSpace ℂ (Lu i))
    (hcomplex : ∀ i, letI := complexChart i; IsManifold 𝓘(ℂ) ∞ (Lu i))
    (hinclusion : ∀ i, letI := complexChart i;
      ContMDiff 𝓘(ℂ) (complexModel d) ∞ (U.leaf i).inclusion ∧
      ∀ z, Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) (U.leaf i).inclusion z))
    (qu : ιu) (qs : ιs) :
    letI := complexChart qu
    ∀ (Pu : TopologicalSpace.Opens (Lu qu)) (Ps : TopologicalSpace.Opens (Ls qs))
      (O : TopologicalSpace.Opens X) (Ψ : (Pu × Ps) ≃ₜ O)
      (c : OpenPartialHomeomorph Pu ℂ),
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ c c.source →
      (∀ s : Ps, ∃ qi : ιu, letI := complexChart qi
        ∃ (V : TopologicalSpace.Opens (Lu qi))
          (b : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) Pu V ∞),
          ∀ u : Pu, (U.leaf qi).inclusion (b u).val = (Ψ (u, s)).val) →
      (∀ u : Pu, ∃ (qi : ιs) (V : TopologicalSpace.Opens (Ls qi)) (b : Ps ≃ₜ V),
        ∀ s : Ps, (S.leaf qi).inclusion (b s).val = (Ψ (u, s)).val) →
      ∀ (W : TopologicalSpace.Opens X) (q : X → ℂ), W ≤ O →
        (∀ u s, (Ψ (u, s)).val ∈ W ↔ u ∈ c.source) →
        ContinuousOn q W → (∀ u s, q (Ψ (u, s)).val = c u) →
        MDifferentiableOn (complexModel d) 𝓘(ℂ) q W := by
  intro Pu Ps O Ψ c hc hreceivingU hreceivingS W q hWO hWslice hqcont hqslice
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨hmetric, hhmetric, C, rate, hC, hr0, hr1, hgrowthS, hgrowthU⟩ :=
    native_unstable_hermitian_growth_exists f a
  have hstableJ := StableFoliationsSupport.original_stable_J_invariant
    f hmetric a.splitting C rate hC ⟨hr0, hr1⟩ hgrowthS hgrowthU
  have hstableComplex (x : X) : ∃ K : Submodule ℂ (TangentSpace (complexModel d) x),
      (K.restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap =
          a.splitting.stable.toDistribution x := by
    obtain ⟨K, hK, _⟩ := StableFoliationsSupport.existsUnique_complexSubmodule_of_J_invariant
      (complexTangentToReal d x).toLinearEquiv (a.splitting.stable.toDistribution x)
      (hstableJ x)
    exact ⟨K, hK⟩
  choose stableComplexFibre hstableComplexFibre using hstableComplex
  intro y hy
  let yo : O := ⟨y, hWO hy⟩
  let u := (Ψ.symm yo).1
  let s := (Ψ.symm yo).2
  have hys : (Ψ (u, s)).val = y :=
    congrArg Subtype.val (Ψ.apply_symm_apply yo)
  have huc : u ∈ c.source := (hWslice u s).mp (hys.symm ▸ hy)
  have hcurve : ∃ qi : ιu, letI := complexChart qi
      ∃ (V : TopologicalSpace.Opens (Lu qi)) (v : V),
        (U.leaf qi).inclusion v.val = y ∧
        ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞
          (fun w : V ↦ q ((U.leaf qi).inclusion w.val)) v := by
    obtain ⟨qi, hrec⟩ := hreceivingU s
    let := complexChart qi
    obtain ⟨V, b, hb⟩ := hrec
    refine ⟨qi, V, b u, (hb u).trans hys, ?_⟩
    have heq : (fun w : V ↦ q ((U.leaf qi).inclusion w.val)) = c ∘ b.symm := by
      funext w
      change q ((U.leaf qi).inclusion w.val) = c (b.symm w)
      have hw := hb (b.symm w)
      rw [b.apply_symm_apply] at hw
      rw [hw, hqslice]
    rw [heq]
    apply (hc.comp b.symm.contMDiff.contMDiffOn (fun _ hw ↦ hw)).contMDiffAt
    apply (c.open_source.preimage b.symm.contMDiff.continuous).mem_nhds
    change b.symm (b u) ∈ c.source
    simpa only [b.symm_apply_apply] using huc
  have hstable : ∃ (qi : ιs) (v : Ls qi),
      (S.leaf qi).inclusion v = y ∧
      (q ∘ (S.leaf qi).inclusion) =ᶠ[𝓝 v] fun _ ↦ q y := by
    obtain ⟨qi, V, b, hb⟩ := hreceivingS u
    refine ⟨qi, (b s).val, (hb s).trans hys, ?_⟩
    filter_upwards [V.isOpen.mem_nhds (b s).property] with z hz
    have hrec := hb (b.symm ⟨z, hz⟩)
    rw [b.apply_symm_apply] at hrec
    change q ((S.leaf qi).inclusion z) = q y
    rw [hrec, hqslice, ← hys, hqslice]
  have complex_of_real
      (hreal : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) q y) :
      MDifferentiableAt (complexModel d) 𝓘(ℂ) q y := by
    let L : TangentSpace (complexModel d) y →L[ℝ] ℂ := mfderiv (realModel d) 𝓘(ℝ, ℂ) q y
    let Ks := stableComplexFibre y
    obtain ⟨Ku, hKuDim, hKuReal⟩ := hRank y
    have hcompl : IsCompl Ks Ku := by
      apply (Submodule.isCompl_restrictScalars_iff ℝ).mp
      apply (Submodule.orderIsoMapComap
        (complexTangentToReal d y).toLinearEquiv).isCompl_iff.mpr
      change IsCompl ((Ks.restrictScalars ℝ).map
          (complexTangentToReal d y).toLinearEquiv.toLinearMap)
        ((Ku.restrictScalars ℝ).map
          (complexTangentToReal d y).toLinearEquiv.toLinearMap)
      rw [hstableComplexFibre y, hKuReal]
      exact a.splitting.isCompl y
    have hkill : ∀ w ∈ Ks, L w = 0 := by
      obtain ⟨i, z, hiz, hcst⟩ := hstable
      have hzero := hcst.mfderiv_eq
        (I := 𝓘(ℝ, Fin (2 * d - 2) → ℝ)) (I' := 𝓘(ℝ, ℂ))
      have hrealz : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) q
          ((S.leaf i).inclusion z) := hiz.symm ▸ hreal
      rw [mfderiv_const, mfderiv_comp z hrealz
        ((S.leaf i).immersion.contMDiff.mdifferentiable (by simp) z)] at hzero
      intro w hw
      have hwreal : complexTangentToReal d y w ∈ a.splitting.stable.toDistribution y := by
        rw [← hstableComplexFibre y]
        exact ⟨w, hw, rfl⟩
      rw [← hiz, ← (S.leaf i).tangent z] at hwreal
      obtain ⟨v, hv⟩ := hwreal
      have he := DFunLike.congr_fun hzero v
      change mfderiv (realModel d) 𝓘(ℝ, ℂ) q ((S.leaf i).inclusion z)
        (mfderiv 𝓘(ℝ, Fin (2 * d - 2) → ℝ) (realModel d)
          (S.leaf i).inclusion z v) = 0 at he
      change (mfderiv 𝓘(ℝ, Fin (2 * d - 2) → ℝ) (realModel d)
        (S.leaf i).inclusion z) v = _ at hv
      rw [hv] at he
      rw [hiz] at he
      exact he
    obtain ⟨i, hci⟩ := hcurve
    let := complexChart i
    let := hcomplex i
    obtain ⟨V, z, hiz, hqc⟩ := hci
    have hqc' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞
        (q ∘ (U.leaf i).inclusion) z.val :=
      contMDiffAt_subtype_iff.mp hqc
    have hi := (hinclusion i).1.contMDiffAt (x := z.val)
    have hir : ContMDiffAt 𝓘(ℝ, ℂ) (realModel d) ∞
        (U.leaf i).inclusion z.val := by
      obtain ⟨hc₀, hd₀⟩ := contMDiffAt_iff.mp hi
      exact contMDiffAt_iff.mpr ⟨hc₀, hd₀.restrict_scalars ℝ⟩
    have hident : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℝ) ∞
        (id : Lu i → Lu i) z.val := by
      apply (ContMDiffAt.iff_comp_isImmersionAt (f := id) (x := z.val)
        ((U.leaf i).immersion.isImmersionAt z.val)).mpr
      exact ⟨continuousAt_id, hir⟩
    let A : ℂ →L[ℂ] TangentSpace (complexModel d) y := mfderiv 𝓘(ℂ) (complexModel d) (U.leaf i).inclusion z.val
    let B : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) (q ∘ (U.leaf i).inclusion) z.val
    have hAi : HasMFDerivAt 𝓘(ℝ, ℂ) (realModel d) (U.leaf i).inclusion z.val
        (A.restrictScalars ℝ) := by
      have h := (hi.mdifferentiableAt (by simp)).hasMFDerivAt
      exact ⟨h.1, h.2.restrictScalars ℝ⟩
    have hBi : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
        (q ∘ (U.leaf i).inclusion) z.val (B.restrictScalars ℝ) := by
      have h := (hqc'.mdifferentiableAt (by simp)).hasMFDerivAt
      exact ⟨h.1, h.2.restrictScalars ℝ⟩
    have hAtan : ∀ v, A v ∈ Ku := by
      intro v
      have he := mfderiv_comp (I := 𝓘(ℝ, ℂ))
        (I' := 𝓘(ℝ, Fin 2 → ℝ)) (I'' := realModel d) z.val
        ((U.leaf i).immersion.contMDiff.mdifferentiable (by simp) z.val)
        (hident.mdifferentiableAt (by simp))
      rw [Function.comp_id, hAi.mfderiv] at he
      have hv : complexTangentToReal d y (A v) ∈
          a.splitting.unstable.toDistribution y := by
        rw [← hiz, ← (U.leaf i).tangent z.val]
        refine ⟨mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℝ) id z.val v, ?_⟩
        exact (DFunLike.congr_fun he v).symm
      rw [← hKuReal] at hv
      obtain ⟨w, hw, hew⟩ := hv
      exact (complexTangentToReal d y).injective hew ▸ hw
    have : FiniteDimensional ℂ (TangentSpace (complexModel d) y) :=
      (tangentSpaceCastModel (complexModel d) y).finiteDimensional
    have hArange : A.range = Ku := by
      apply Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨v, rfl⟩; exact hAtan v)
      rw [LinearMap.finrank_range_of_inj (show Function.Injective A from (hinclusion i).2 z.val)]
      exact (Module.finrank_self ℂ).trans hKuDim.symm
    have hchain : L.comp (A.restrictScalars ℝ) = B.restrictScalars ℝ := by
      have hrealz : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) q
          ((U.leaf i).inclusion z.val) := hiz.symm ▸ hreal
      have he := mfderiv_comp z.val hrealz hAi.mdifferentiableAt
      rw [hAi.mfderiv, hBi.mfderiv, hiz] at he
      exact he.symm
    have hUlinear : ∀ t : ℂ, ∀ w ∈ Ku, L (t • w) = t • L w := by
      intro t w hw
      rw [← hArange] at hw
      obtain ⟨v, rfl⟩ := hw
      change L (t • A v) = t • L (A v)
      rw [← map_smul A t v]
      have he (v) := DFunLike.congr_fun hchain v
      have he' (v) : L (A v) = B v := he v
      rw [he', he', B.map_smul]
    have hlinear (t : ℂ) (w : TangentSpace (complexModel d) y) :
        L (t • w) = t • L w := by
      have hw : w ∈ Ks ⊔ Ku := by rw [hcompl.sup_eq_top]; trivial
      obtain ⟨vs, hvs, vu, hvu, rfl⟩ := Submodule.mem_sup.mp hw
      rw [smul_add, L.map_add, L.map_add, hkill vs hvs,
        hkill (t • vs) (Ks.smul_mem t hvs), hUlinear t vu hvu]
      simp
    let K : TangentSpace (complexModel d) y →L[ℂ] ℂ :=
      { toFun := L
        map_add' := L.map_add
        map_smul' := hlinear
        cont := L.continuous }
    have hK : HasMFDerivAt (complexModel d) 𝓘(ℂ) q y K := by
      refine ⟨hreal.continuousAt, ?_⟩
      have hr : HasFDerivAt
          (writtenInExtChartAt (complexModel d) 𝓘(ℂ) y q) L
          (extChartAt (complexModel d) y y) := by
        convert hreal.hasMFDerivAt.2.hasFDerivAt (by simp) using 1 <;> rfl
      exact (hasFDerivAt_of_restrictScalars ℝ hr (show K.restrictScalars ℝ = L from rfl)).hasFDerivWithinAt
    exact hK.mdifferentiableAt
  apply (complex_of_real ?_).mdifferentiableWithinAt
  let := hcomplex qu
  obtain ⟨is, Vs, bs, hbs⟩ := hreceivingS u
  let vs : Ls is := (bs s).val
  let eu := chartAt ℂ u
  let es : OpenPartialHomeomorph Ps (Fin (2*d-2) → ℝ) :=
    bs.toOpenPartialHomeomorph.trans
      ((Vs.openPartialHomeomorphSubtypeCoe ⟨bs s⟩).trans
        (chartAt (Fin (2*d-2) → ℝ) vs))
  let ex := chartAt (ComplexModel d) y
  let H : OpenPartialHomeomorph (ℂ × (Fin (2*d-2) → ℝ)) (ComplexModel d) :=
    (eu.prod es).symm.trans
      (Ψ.toOpenPartialHomeomorph.trans
        ((O.openPartialHomeomorphSubtypeCoe ⟨yo⟩).trans ex))
  let p := (eu u, es s)
  have hu : u ∈ eu.source := mem_chart_source ℂ u
  have hs : s ∈ es.source := by
    simp [es, vs]
  have he : (u,s) ∈ (eu.prod es).source := ⟨hu, hs⟩
  have hHsource : p ∈ H.source := by
    have hep : (eu.prod es).symm p = (u,s) := (eu.prod es).left_inv he
    change p ∈ (eu.prod es).target ∧
      (eu.prod es).symm p ∈ (Ψ.toOpenPartialHomeomorph.trans
        ((O.openPartialHomeomorphSubtypeCoe ⟨yo⟩).trans ex)).source
    rw [hep]
    refine ⟨(eu.prod es).map_source he, trivial, trivial, ?_⟩
    change (Ψ (u,s)).val ∈ ex.source
    rw [hys]
    exact mem_chart_source _ y
  have hHp : H p = ex y := by
    change ex ((Ψ ((eu.prod es).symm ((eu.prod es) (u,s)))).val) = ex y
    rw [(eu.prod es).left_inv he, hys]
  have hFu (t : Ps) : ContMDiff 𝓘(ℂ) (complexModel d) ∞
      (fun z : Pu ↦ (Ψ (z,t)).val) := by
    obtain ⟨i, hi⟩ := hreceivingU t
    let := complexChart i
    let := hcomplex i
    obtain ⟨V, b, hb⟩ := hi
    have hm := (hinclusion i).1.comp (contMDiff_subtype_val.comp b.contMDiff)
    exact hm.congr (fun z ↦ (hb z).symm)
  have hhol : ∀ t, DifferentiableOn ℂ (fun z ↦ H (z,t))
      {z | (z,t) ∈ H.source} := by
    intro t z hz
    have hzt : (z,t) ∈ (eu.prod es).target := hz.1
    have hzx : (Ψ (eu.symm z, es.symm t)).val ∈ ex.source := hz.2.2.2
    have h1 := ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ∞) (x := u)).contMDiffAt
      (eu.open_target.mem_nhds hzt.1)).mdifferentiableAt (by simp)
    have h2 := (hFu (es.symm t)).mdifferentiable (by simp) (eu.symm z)
    have h3 := (contMDiffOn_chart (I := complexModel d) (n := ∞) (x := y)).contMDiffAt
      (ex.open_source.mem_nhds hzx)
    have hh := (h3.mdifferentiableAt (by simp)).comp z (h2.comp z h1)
    exact hh.differentiableAt.differentiableWithinAt
  have hsv : (S.leaf is).inclusion vs = y := (hbs s).trans hys
  let B : (Fin (2*d-2) → ℝ) →L[ℝ] TangentSpace (realModel d) y :=
    mfderiv 𝓘(ℝ, Fin (2*d-2) → ℝ) (realModel d) (S.leaf is).inclusion vs
  have hes (t) (ht : t ∈ es.target) :
      (bs (es.symm t)).val = (chartAt (Fin (2*d-2) → ℝ) vs).symm t := by
    have hmem := es.map_target ht
    have hchart : (bs (es.symm t)).val ∈ (chartAt (Fin (2*d-2) → ℝ) vs).source := hmem.2.2
    have heq : (chartAt (Fin (2*d-2) → ℝ) vs) (bs (es.symm t)).val = t := es.right_inv ht
    calc
      _ = (chartAt (Fin (2*d-2) → ℝ) vs).symm
          ((chartAt (Fin (2*d-2) → ℝ) vs) (bs (es.symm t)).val) :=
        ((chartAt (Fin (2*d-2) → ℝ) vs).left_inv hchart).symm
      _ = _ := congrArg _ heq
  have hB : HasFDerivAt (fun t ↦ H (p.1,t)) B p.2 := by
    have hi := ((S.leaf is).immersion.contMDiff.mdifferentiable (by simp) vs).hasMFDerivAt
    have hbase : HasFDerivAt
        (writtenInExtChartAt 𝓘(ℝ, Fin (2*d-2) → ℝ) (realModel d) vs
          (S.leaf is).inclusion) B p.2 := hi.2.hasFDerivAt (by simp)
    apply hbase.congr_of_eventuallyEq
    filter_upwards [es.open_target.mem_nhds (es.map_source hs)] with t ht
    simp only [writtenInExtChartAt, Function.comp_apply, hsv]
    change H (eu u,t) = ex ((S.leaf is).inclusion
      ((chartAt (Fin (2*d-2) → ℝ) vs).symm t))
    change ex (Ψ (eu.symm (eu u),es.symm t)).val = _
    rw [eu.left_inv hu, ← hbs, hes t ht]
  have hAB := HolomorphicAnosov.Analysis.hasFDerivAt_holomorphic_product H H.source
    H.open_source H.continuousOn hhol p.1 p.2 hHsource B hB
  let R : ℂ →L[ℂ] TangentSpace (complexModel d) y :=
    mfderiv 𝓘(ℂ) (complexModel d) (fun z : Pu ↦ (Ψ (z,s)).val) u
  have hR : HasFDerivAt (fun z ↦ H (z,p.2)) R p.1 := by
    have hi := ((hFu s).mdifferentiable (by simp) u).hasMFDerivAt
    have hbase : HasFDerivAt
        (writtenInExtChartAt 𝓘(ℂ) (complexModel d) u
          (fun z : Pu ↦ (Ψ (z,s)).val)) R p.1 := hi.2.hasFDerivAt (by simp)
    convert hbase using 1
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply, hys]
    change ex (Ψ (eu.symm z, es.symm (es s))).val = ex (Ψ (eu.symm z,s)).val
    rw [es.left_inv hs]
  rw [hR.fderiv] at hAB
  obtain ⟨iu, hiu⟩ := hreceivingU s
  let := complexChart iu
  let := hcomplex iu
  obtain ⟨Vu, bu, hbu⟩ := hiu
  let gu : Pu → Lu iu := fun z ↦ (bu z).val
  have hgu : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ gu := contMDiff_subtype_val.comp bu.contMDiff
  have hgueq : (U.leaf iu).inclusion ∘ gu = (fun z : Pu ↦ (Ψ (z,s)).val) := funext hbu
  have hguy : (U.leaf iu).inclusion (gu u) = y := (hbu u).trans hys
  have hRinj : Function.Injective R := by
    change Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) _ u)
    rw [← hgueq, mfderiv_comp u ((hinclusion iu).1.mdifferentiable (by simp) _)
      (hgu.mdifferentiable (by simp) _)]
    have hginj : Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ) gu u) := by
      change Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ) (Subtype.val ∘ bu) u)
      rw [mfderiv_comp u ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) _)
        (bu.mdifferentiable (by simp) _)]
      exact (openSubsetInclusion_mfderiv_bijective 𝓘(ℂ) Vu (bu u)).injective.comp
        ((bu.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective (by simp))
    exact ((hinclusion iu).2 (gu u)).comp hginj
  have hRreal : HasMFDerivAt 𝓘(ℝ, ℂ) (realModel d)
      (fun z : Pu ↦ (Ψ (z,s)).val) u (R.restrictScalars ℝ) := by
    have hi := ((hFu s).mdifferentiable (by simp) u).hasMFDerivAt
    exact ⟨hi.1, hi.2.restrictScalars ℝ⟩
  have hgr : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℝ) ∞ gu u := by
    apply (ContMDiffAt.iff_comp_isImmersionAt
      ((U.leaf iu).immersion.isImmersionAt (gu u))).mpr
    refine ⟨hgu.continuous.continuousAt, ?_⟩
    rw [hgueq]
    obtain ⟨ht, hd'⟩ := contMDiffAt_iff.mp ((hFu s).contMDiffAt (x := u))
    exact contMDiffAt_iff.mpr ⟨ht, hd'.restrict_scalars ℝ⟩
  let A : ℂ →L[ℝ] TangentSpace (realModel d) y :=
    (complexTangentToReal d y).toContinuousLinearMap.comp (R.restrictScalars ℝ)
  have hAinj : Function.Injective A := (complexTangentToReal d y).injective.comp hRinj
  have hRrange : A.range = a.splitting.unstable.toDistribution y := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro w ⟨v, rfl⟩
      have hchain := mfderiv_comp u
        ((U.leaf iu).immersion.contMDiff.mdifferentiable (by simp) (gu u))
        (hgr.mdifferentiableAt (by simp))
      rw [hgueq, hRreal.mfderiv] at hchain
      have hv : A v ∈
          a.splitting.unstable.toDistribution ((U.leaf iu).inclusion (gu u)) := by
        rw [← (U.leaf iu).tangent (gu u)]
        refine ⟨mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℝ) gu u v, ?_⟩
        exact (DFunLike.congr_fun hchain v).symm
      rw [hguy] at hv
      exact hv
    · rw [LinearMap.finrank_range_of_inj hAinj]
      have hdim := LinearMap.finrank_range_of_inj
        ((U.leaf iu).immersion.mfderiv_injective (by simp) (gu u))
      rw [(U.leaf iu).tangent (gu u), hguy] at hdim
      rw [hdim]
      change Module.finrank ℝ ℂ = Module.finrank ℝ (Fin 2 → ℝ)
      simp
  have hBrange : B.range = a.splitting.stable.toDistribution y := by
    change (mfderiv 𝓘(ℝ, Fin (2*d-2) → ℝ) (realModel d) (S.leaf is).inclusion vs).range = _
    rw [(S.leaf is).tangent vs, hsv]
  have hBinj : Function.Injective B := (S.leaf is).immersion.mfderiv_injective (by simp) vs
  have hcompl : IsCompl A.range B.range := by
    rw [hRrange, hBrange]
    exact (a.splitting.isCompl y).symm
  have hbij : Function.Bijective (A.coprod B) := by
    change Function.Bijective (A.toLinearMap.coprod B.toLinearMap)
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range _ _ hcompl.disjoint,
        LinearMap.ker_eq_bot.mpr hAinj,
        LinearMap.ker_eq_bot.mpr hBinj]
      simp
    · rw [← LinearMap.range_eq_top, LinearMap.range_coprod]
      exact hcompl.sup_eq_top
  let Q : ComplexModel d → ℂ := q ∘ ex.symm
  have hcc : DifferentiableAt ℂ (c ∘ eu.symm) p.1 := by
    have h1 := (hc.contMDiffAt (c.open_source.mem_nhds huc)).mdifferentiableAt (by simp)
    have h2 := ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ∞) (x := u)).contMDiffAt
      (eu.open_target.mem_nhds (eu.map_source hu))).mdifferentiableAt (by simp)
    have h1' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) c (eu.symm (eu u)) := by
      simpa only [eu.left_inv hu] using h1
    exact (h1'.comp _ h2).differentiableAt
  have hqH : DifferentiableAt ℝ (Q ∘ H) p := by
    have hd' := (hcc.restrictScalars ℝ).comp p differentiableAt_fst
    apply hd'.congr_of_eventuallyEq
    filter_upwards [H.open_source.mem_nhds hHsource] with z hz
    have hz' : (Ψ (eu.symm z.1,es.symm z.2)).val ∈ ex.source := hz.2.2.2
    change q (ex.symm (ex (Ψ (eu.symm z.1,es.symm z.2)).val)) = c (eu.symm z.1)
    rw [ex.left_inv hz', hqslice]
  have hQ := HolomorphicAnosov.Analysis.differentiableAt_of_comp_product_chart
    H p hHsource (A.coprod B) hAB hbij Q hqH
  rw [hHp] at hQ
  exact (mdifferentiableAt_iff (I := realModel d) (I' := 𝓘(ℝ, ℂ)) q y).mpr ⟨hqcont.continuousAt (W.isOpen.mem_nhds hy), by
    simpa only [writtenInExtChartAt, mfld_simps] using hQ.differentiableWithinAt⟩

end HolomorphicAnosov.Ghys

