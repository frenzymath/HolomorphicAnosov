import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveProductDevelopment
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Geometry.ComplexProjectiveLine
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Geometry.Manifold.ZeroMFDerivConstancy
import HolomorphicAnosov.Analysis.Complex.LeblInjectiveHolomorphicBiholomorphism

/-!
# Local ordered product charts inside a supplied projective atlas

Given an ordered projective atlas, this file constructs local biholomorphic product charts from transverse stable and unstable plaques (Ghys, p. 598; Lee, Prop. 19.12; Lebl, Thm. 1.6.5).
-/

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter _root_.HolomorphicAnosov.Topology _root_.Topology
open scoped ContDiff Manifold

/-- An injective holomorphic map into an original surface chart extends to a biholomorphic partial homeomorphism on its open domain (Lebl, Thm. 1.6.5). -/
theorem surface_chart_of_holomorphic_injection
    {S : Type*} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    {D : Set (ℂ × ℂ)} (hD : IsOpen D) (F : ℂ × ℂ → S)
    (hF : ContMDiffOn 𝓘(ℂ, ℂ × ℂ) (complexModel 2) ∞ F D)
    (hinj : InjOn F D) (c : OpenPartialHomeomorph S (ComplexModel 2))
    (hFc : MapsTo F D c.source)
    (hc : ContMDiffOn (complexModel 2) (complexModel 2) ∞ c c.source) :
    ∃ e : OpenPartialHomeomorph (ℂ × ℂ) S,
      e.source = D ∧ (∀ z ∈ D, e z = F z) ∧
      ContMDiffOn 𝓘(ℂ, ℂ × ℂ) (complexModel 2) ∞ e e.source ∧
      ContMDiffOn (complexModel 2) 𝓘(ℂ, ℂ × ℂ) ∞ e.symm e.target := by
  let q : (Fin 2 → ℂ) ≃L[ℂ] ℂ × ℂ := ContinuousLinearEquiv.finTwoArrow ℂ ℂ
  let U := q ⁻¹' D
  let H := c ∘ F ∘ q
  have hU : IsOpen U := hD.preimage q.continuous
  have hH : ContDiffOn ℂ ∞ H U :=
    (hc.comp (hF.comp q.contDiff.contMDiff.contMDiffOn (fun _ hz ↦ hz))
      (fun z hz ↦ hFc hz)).contDiffOn
  have hHi : InjOn H U := by
    intro z hz w hw he
    exact q.injective (hinj hz hw (c.injOn (hFc hz) (hFc hw) he))
  obtain ⟨_, hV, G, hG, hleft, hright⟩ :=
    lebl_injective_holomorphic_biholomorphism (by decide : 0 < 2) hU
      (hH.differentiableOn (by simp)) hHi
  have hGs : ContDiffOn ℂ ∞ G (H '' U) :=
    (complex_contDiffOn_iff_differentiableOn hV).mpr hG
  let p : OpenPartialHomeomorph (ℂ × ℂ) (ComplexModel 2) :=
    { toFun := c ∘ F
      invFun := q ∘ G
      source := D
      target := H '' U
      map_source' := by
        intro z hz
        exact ⟨q.symm z, by simpa [U] using hz, by simp [H]⟩
      map_target' := fun w hw ↦ (hright w hw).1
      left_inv' := by
        intro z hz
        have hz' : q.symm z ∈ U := by simpa [U] using hz
        have hl := congrArg q (hleft (q.symm z) hz')
        simpa [H] using hl
      right_inv' := fun w hw ↦ (hright w hw).2
      open_source := hD
      open_target := hV
      continuousOn_toFun := (hc.comp hF hFc).continuousOn
      continuousOn_invFun := q.continuous.comp_continuousOn hG.continuousOn }
  have hpct : p.target ⊆ c.target := by
    rintro w ⟨z, hz, rfl⟩
    exact c.map_source (hFc hz)
  let e := p.trans c.symm
  have heS : e.source = D := by
    ext z
    exact ⟨fun hz ↦ hz.1, fun hz ↦ ⟨hz, hpct (p.map_source hz)⟩⟩
  have heF : ∀ z ∈ D, e z = F z := by
    intro z hz
    exact c.left_inv (hFc hz)
  refine ⟨e, heS, heF, ?_, ?_⟩
  · rw [heS]
    exact hF.congr (fun z hz ↦ heF z hz)
  · have heT : e.target ⊆ c.source := fun _ hz ↦ hz.1
    have hmaps : MapsTo c e.target p.target := fun _ hz ↦ hz.2
    have hqG : ContMDiffOn (complexModel 2) 𝓘(ℂ, ℂ × ℂ) ∞ (q ∘ G) p.target :=
      (q.contDiff.comp_contDiffOn hGs).contMDiffOn
    exact hqG.comp (hc.mono heT) hmaps

attribute [local instance] complex_isManifold_real

/-- A transverse coordinate is constant along a connected plaque when its derivative vanishes on the plaque tangent space (Lee, Prop. 19.12). -/
theorem surface_plaque_coordinate_constant
    {S : Type*} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    (α : ℂ → S) (φ : S → ComplexProjectiveLine)
    {r : ℝ} (hr : 0 < r) {V : Set S} (hV : IsOpen V)
    (hα : ContMDiffOn 𝓘(ℂ) (complexModel 2) ∞ α (Metric.ball 0 r))
    (hφ : ContMDiffOn (complexModel 2) (complexModel 1) ∞ φ V)
    (hm : MapsTo α (Metric.ball 0 r) V)
    (hker : ∀ z ∈ Metric.ball (0 : ℂ) r,
      LinearMap.range (mfderiv 𝓘(ℝ, ℂ) (realModel 2) α z).toLinearMap ≤
        LinearMap.ker (mfderiv (realModel 2) (realModel 1) φ (α z)).toLinearMap) :
    ∀ z ∈ Metric.ball (0 : ℂ) r, φ (α z) = φ (α 0) := by
  have hαr (z : ℂ) (hz : z ∈ Metric.ball 0 r) :
      MDifferentiableAt 𝓘(ℝ, ℂ) (realModel 2) α z := by
    have h := (hα z hz).contMDiffAt (Metric.isOpen_ball.mem_nhds hz)
    obtain ⟨hc, hd⟩ := contMDiffAt_iff.mp h
    exact (contMDiffAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩ :
      ContMDiffAt 𝓘(ℝ, ℂ) (realModel 2) ∞ α z).mdifferentiableAt (by simp)
  have hφr (z : ℂ) (hz : z ∈ Metric.ball 0 r) :
      MDifferentiableAt (realModel 2) (realModel 1) φ (α z) := by
    have h := (hφ (α z) (hm hz)).contMDiffAt (hV.mem_nhds (hm hz))
    obtain ⟨hc, hd⟩ := contMDiffAt_iff.mp h
    exact (contMDiffAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩ :
      ContMDiffAt (realModel 2) (realModel 1) ∞ φ (α z)).mdifferentiableAt (by simp)
  have hd : MDifferentiableOn 𝓘(ℝ, ℂ) (realModel 1) (φ ∘ α) (Metric.ball 0 r) :=
    fun z hz ↦ ((hφr z hz).comp z (hαr z hz)).mdifferentiableWithinAt
  have hz : ∀ z ∈ Metric.ball (0 : ℂ) r,
      mfderiv 𝓘(ℝ, ℂ) (realModel 1) (φ ∘ α) z = 0 := by
    intro z hz
    rw [mfderiv_comp z (hφr z hz) (hαr z hz)]
    ext v
    exact hker z hz ⟨v, rfl⟩
  intro z hzr
  exact eq_of_mfderiv_eq_zero_on Metric.isOpen_ball (convex_ball (0 : ℂ) r).isPreconnected
    (φ ∘ α) hd hz hzr (Metric.mem_ball_self hr)

end HolomorphicAnosov.Ghys


namespace HolomorphicAnosov.Ghys
open Set Filter _root_.HolomorphicAnosov.Topology _root_.Topology
open scoped ContDiff Manifold
attribute [local instance] complex_isManifold_real

/-- Two transverse holomorphic plaques in an ordered product chart determine a local biholomorphic product chart with the prescribed axes and unique intersections (Ghys, p. 598; Lee, Prop. 19.12; Lebl, Thm. 1.6.5). -/
theorem surface_local_product_in_chart
    {S : Type*} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    (c : OpenPartialHomeomorph S (ComplexProjectiveLine × ComplexProjectiveLine))
    (hc : ContMDiffOn (complexModel 2) ((complexModel 1).prod (complexModel 1)) ∞ c c.source)
    (hci : ContMDiffOn ((complexModel 1).prod (complexModel 1)) (complexModel 2) ∞ c.symm c.target)
    (x : S) (hx : x ∈ c.source) (α β : ℂ → S) (rα rβ : ℝ)
    (hrα : 0 < rα) (hrβ : 0 < rβ) (hα0 : α 0 = x) (hβ0 : β 0 = x)
    (hα : ContMDiffOn 𝓘(ℂ) (complexModel 2) ∞ α (Metric.ball 0 rα))
    (hβ : ContMDiffOn 𝓘(ℂ) (complexModel 2) ∞ β (Metric.ball 0 rβ))
    (hiα : IsEmbedding (fun z : ↥(Metric.ball (0 : ℂ) rα) ↦ α z))
    (hiβ : IsEmbedding (fun z : ↥(Metric.ball (0 : ℂ) rβ) ↦ β z))
    (hkα : ∀ z ∈ Metric.ball (0 : ℂ) rα, α z ∈ c.source →
      LinearMap.range (mfderiv 𝓘(ℝ, ℂ) (realModel 2) α z).toLinearMap ≤
        LinearMap.ker (mfderiv (realModel 2) (realModel 1) (fun y ↦ (c y).2) (α z)).toLinearMap)
    (hkβ : ∀ z ∈ Metric.ball (0 : ℂ) rβ, β z ∈ c.source →
      LinearMap.range (mfderiv 𝓘(ℝ, ℂ) (realModel 2) β z).toLinearMap ≤
        LinearMap.ker (mfderiv (realModel 2) (realModel 1) (fun y ↦ (c y).1) (β z)).toLinearMap) :
    ∃ (r : ℝ) (e : OpenPartialHomeomorph (ℂ × ℂ) S),
      0 < r ∧ r ≤ rα ∧ r ≤ rβ ∧
      e.source = Metric.ball (0 : ℂ) r ×ˢ Metric.ball (0 : ℂ) r ∧
      x ∈ e.target ∧
      ContMDiffOn 𝓘(ℂ, ℂ × ℂ) (complexModel 2) ∞ e e.source ∧
      ContMDiffOn (complexModel 2) 𝓘(ℂ, ℂ × ℂ) ∞ e.symm e.target ∧
      ∀ s ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
        α s ∈ c.source ∧ β w ∈ c.source ∧ e (s,w) ∈ c.source ∧
        c (e (s,w)) = ((c (α s)).1, (c (β w)).2) ∧
        e (s,0) = α s ∧ e (0,w) = β w ∧
        ∀ y ∈ c.source,
          ((c y).1 = (c (α s)).1 ∧ (c y).2 = (c (β w)).2) ↔ y = e (s,w) := by
  have hαc : ContinuousAt α 0 :=
    hα.continuousOn.continuousAt (Metric.ball_mem_nhds 0 hrα)
  have hβc : ContinuousAt β 0 :=
    hβ.continuousOn.continuousAt (Metric.ball_mem_nhds 0 hrβ)
  have hn : Metric.ball (0 : ℂ) rα ∩ Metric.ball (0 : ℂ) rβ ∩
      α ⁻¹' c.source ∩ β ⁻¹' c.source ∈ 𝓝 0 := by
    exact inter_mem (inter_mem (inter_mem (Metric.ball_mem_nhds 0 hrα)
      (Metric.ball_mem_nhds 0 hrβ))
      (hαc.preimage_mem_nhds (c.open_source.mem_nhds (hα0.symm ▸ hx))))
      (hβc.preimage_mem_nhds (c.open_source.mem_nhds (hβ0.symm ▸ hx)))
  obtain ⟨t, ht, hts⟩ := Metric.mem_nhds_iff.mp hn
  have htα : Metric.ball (0 : ℂ) t ⊆ Metric.ball 0 rα := fun _ hz ↦ (hts hz).1.1.1
  have htβ : Metric.ball (0 : ℂ) t ⊆ Metric.ball 0 rβ := fun _ hz ↦ (hts hz).1.1.2
  have hmα : MapsTo α (Metric.ball (0 : ℂ) t) c.source := fun _ hz ↦ (hts hz).1.2
  have hmβ : MapsTo β (Metric.ball (0 : ℂ) t) c.source := fun _ hz ↦ (hts hz).2
  have hconstα := surface_plaque_coordinate_constant α (fun y ↦ (c y).2) ht c.open_source
    (hα.mono htα) (fun z hz ↦ (hc z hz).snd) hmα
    (fun z hz ↦ hkα z (htα hz) (hmα hz))
  have hconstβ := surface_plaque_coordinate_constant β (fun y ↦ (c y).1) ht c.open_source
    (hβ.mono htβ) (fun z hz ↦ (hc z hz).fst) hmβ
    (fun z hz ↦ hkβ z (htβ hz) (hmβ hz))
  let P : ℂ × ℂ → ComplexProjectiveLine × ComplexProjectiveLine :=
    fun z ↦ ((c (α z.1)).1, (c (β z.2)).2)
  let T : Set (ℂ × ℂ) := Metric.ball (0 : ℂ) t ×ˢ Metric.ball (0 : ℂ) t
  have hP : ContMDiffOn 𝓘(ℂ, ℂ × ℂ) ((complexModel 1).prod (complexModel 1)) ∞ P T := by
    have ha := (hc.comp (hα.mono htα) hmα).comp
      contDiff_fst.contMDiff.contMDiffOn (fun z (hz : z ∈ T) ↦ hz.1)
    have hb := (hc.comp (hβ.mono htβ) hmβ).comp
      contDiff_snd.contMDiff.contMDiffOn (fun z (hz : z ∈ T) ↦ hz.2)
    exact (fun z hz ↦ (ha z hz).fst.prodMk (hb z hz).snd)
  have hP0 : P (0,0) = c x := by simp [P, hα0, hβ0]
  let d := chartAt (ComplexModel 2) x
  have hd0 : x ∈ d.source := mem_chart_source _ x
  have hV : IsOpen (c.target ∩ c.symm ⁻¹' d.source) :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target d.open_source
  have hV0 : P (0,0) ∈ c.target ∩ c.symm ⁻¹' d.source := by
    rw [hP0]
    exact ⟨c.map_source hx, by simpa [c.left_inv hx] using hd0⟩
  have hPc : ContinuousAt P (0,0) :=
    hP.continuousOn.continuousAt ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds
      ⟨Metric.mem_ball_self ht, Metric.mem_ball_self ht⟩)
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (hPc.preimage_mem_nhds (hV.mem_nhds hV0))
  let r := min ε (min t (min rα rβ))
  have hr : 0 < r := lt_min hε (lt_min ht (lt_min hrα hrβ))
  have hrε : r ≤ ε := min_le_left _ _
  have hrt : r ≤ t := (min_le_right _ _).trans (min_le_left _ _)
  have hrα' : r ≤ rα := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrβ' : r ≤ rβ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let D : Set (ℂ × ℂ) := Metric.ball (0 : ℂ) r ×ˢ Metric.ball (0 : ℂ) r
  have hDT : D ⊆ T := Set.prod_mono (Metric.ball_subset_ball hrt) (Metric.ball_subset_ball hrt)
  have hPV : MapsTo P D (c.target ∩ c.symm ⁻¹' d.source) := by
    intro z hz
    apply hεs
    apply Metric.ball_subset_ball hrε
    simpa only [← ball_prod_same] using (show z ∈ Metric.ball (0 : ℂ) r ×ˢ Metric.ball (0 : ℂ) r from hz)
  let F : ℂ × ℂ → S := c.symm ∘ P
  have hF : ContMDiffOn 𝓘(ℂ, ℂ × ℂ) (complexModel 2) ∞ F D :=
    hci.comp (hP.mono hDT) (fun z hz ↦ (hPV hz).1)
  have hFc : MapsTo F D c.source := fun z hz ↦ c.map_target (hPV hz).1
  have hFd : MapsTo F D d.source := fun z hz ↦ (hPV hz).2
  have hCF : ∀ z ∈ D, c (F z) = P z := fun z hz ↦ c.right_inv (hPV hz).1
  have hFi : InjOn F D := by
    intro z hz v hv he
    have hp : P z = P v := (hCF z hz).symm.trans ((congrArg c he).trans (hCF v hv))
    apply Prod.ext
    · apply congrArg Subtype.val (hiα.injective (a₁ := ⟨z.1, htα (hDT hz).1⟩)
        (a₂ := ⟨v.1, htα (hDT hv).1⟩) ?_)
      apply c.injOn (hmα (hDT hz).1) (hmα (hDT hv).1)
      apply Prod.ext
      · simpa only [P] using congrArg Prod.fst hp
      · exact (hconstα _ (hDT hz).1).trans (hconstα _ (hDT hv).1).symm
    · apply congrArg Subtype.val (hiβ.injective (a₁ := ⟨z.2, htβ (hDT hz).2⟩)
        (a₂ := ⟨v.2, htβ (hDT hv).2⟩) ?_)
      apply c.injOn (hmβ (hDT hz).2) (hmβ (hDT hv).2)
      apply Prod.ext
      · exact (hconstβ _ (hDT hz).2).trans (hconstβ _ (hDT hv).2).symm
      · simpa only [P] using congrArg Prod.snd hp
  have hd : ContMDiffOn (complexModel 2) (complexModel 2) ∞ d d.source :=
    contMDiffOn_chart
  obtain ⟨e, heD, heF, he, hei⟩ := surface_chart_of_holomorphic_injection
    (Metric.isOpen_ball.prod Metric.isOpen_ball) F hF hFi d hFd hd
  have h0 : (0 : ℂ) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  have he0 : e (0,0) = x := by
    rw [heF _ ⟨h0,h0⟩]
    change c.symm (P (0,0)) = x
    rw [hP0, c.left_inv hx]
  refine ⟨r, e, hr, hrα', hrβ', heD, ?_, he, hei, ?_⟩
  · rw [← he0]
    exact e.map_source (heD.symm ▸ show (0,0) ∈ D from ⟨h0,h0⟩)
  intro s hs w hw
  have hsw : (s,w) ∈ D := ⟨hs,hw⟩
  have hsT := Metric.ball_subset_ball hrt hs
  have hwT := Metric.ball_subset_ball hrt hw
  have hec : e (s,w) ∈ c.source := by rw [heF _ hsw]; exact hFc hsw
  have hecoord : c (e (s,w)) = P (s,w) := by rw [heF _ hsw]; exact hCF _ hsw
  refine ⟨hmα hsT, hmβ hwT, hec, hecoord, ?_, ?_, ?_⟩
  · rw [heF _ ⟨hs,h0⟩]
    change c.symm ((c (α s)).1, (c (β 0)).2) = α s
    rw [hβ0, ← hα0, ← hconstα s hsT]
    exact c.left_inv (hmα hsT)
  · rw [heF _ ⟨h0,hw⟩]
    change c.symm ((c (α 0)).1, (c (β w)).2) = β w
    rw [hα0, ← hβ0, ← hconstβ w hwT]
    exact c.left_inv (hmβ hwT)
  · intro y hy
    constructor
    · intro hh
      apply c.injOn hy hec
      calc c y = P (s,w) := by
             apply Prod.ext
             · exact hh.1
             · exact hh.2
           _ = c (e (s,w)) := hecoord.symm
    · rintro rfl
      constructor
      · simpa only [P] using congrArg Prod.fst hecoord
      · simpa only [P] using congrArg Prod.snd hecoord

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open Set _root_.HolomorphicAnosov.Topology _root_.Topology
open scoped ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real

/-- In an ordered projective atlas, sufficiently small stable and unstable plaques around a common point form a biholomorphic product chart whose coordinates agree with the atlas coordinates and have the stated uniqueness property (Ghys, p. 598; Lee, Prop. 19.12; Lebl, Thm. 1.6.5). -/
theorem surface_projective_g3_local_product_chart_bridge_g7
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f)
    (_stable_rank : HasComplexRankOne a.splitting.stable.toDistribution)
    (_unstable_rank : HasComplexRankOne a.splitting.unstable.toDistribution)
    (A : OrderedProjectiveProductAtlas.{u, u} f a) :
∀ (x : S) (α β : ℂ → S) (rα rβ : ℝ),
        0 < rα → 0 < rβ → α 0 = x → β 0 = x →
        ContMDiffOn 𝓘(ℂ) (complexModel 2) ∞ α (Metric.ball 0 rα) →
        ContMDiffOn 𝓘(ℂ) (complexModel 2) ∞ β (Metric.ball 0 rβ) →
        IsEmbedding (fun z : ↥(Metric.ball (0 : ℂ) rα) ↦ α z) →
        IsEmbedding (fun z : ↥(Metric.ball (0 : ℂ) rβ) ↦ β z) →
        (∀ z ∈ Metric.ball (0 : ℂ) rα,
          LinearMap.range (mfderiv 𝓘(ℝ, ℂ) (realModel 2) α z).toLinearMap =
            a.splitting.stable.toDistribution (α z)) →
        (∀ z ∈ Metric.ball (0 : ℂ) rβ,
          LinearMap.range (mfderiv 𝓘(ℝ, ℂ) (realModel 2) β z).toLinearMap =
            a.splitting.unstable.toDistribution (β z)) →
        ∃ (rs ru : ℝ) (e : OpenPartialHomeomorph (ℂ × ℂ) S) (i : A.index),
          0 < rs ∧ rs ≤ rα ∧ 0 < ru ∧ ru ≤ rβ ∧
          e.source = Metric.ball (0 : ℂ) rs ×ˢ Metric.ball (0 : ℂ) ru ∧
          x ∈ e.target ∧
          ContMDiffOn 𝓘(ℂ, ℂ × ℂ) (complexModel 2) ∞ e e.source ∧
          ContMDiffOn (complexModel 2) 𝓘(ℂ, ℂ × ℂ) ∞ e.symm e.target ∧
          ∀ s ∈ Metric.ball (0 : ℂ) rs, ∀ w ∈ Metric.ball (0 : ℂ) ru,
            α s ∈ (A.chart i).source ∧ β w ∈ (A.chart i).source ∧
            e (s, w) ∈ (A.chart i).source ∧
            A.chart i (e (s, w)) = ((A.chart i (α s)).1, (A.chart i (β w)).2) ∧
            e (s, 0) = α s ∧ e (0, w) = β w ∧
            ∀ y ∈ (A.chart i).source,
              ((A.chart i y).1 = (A.chart i (α s)).1 ∧
                (A.chart i y).2 = (A.chart i (β w)).2) ↔ y = e (s, w) := by
  intro x α β rα rβ hrα hrβ hα0 hβ0 hα hβ hiα hiβ hαrange hβrange
  obtain ⟨i, hi⟩ := A.cover x
  obtain ⟨r, e, hr, hrα', hrβ', hsource, hx, he, hei, hspec⟩ :=
    surface_local_product_in_chart (A.chart i) (A.holomorphic i).1 (A.holomorphic i).2
      x hi α β rα rβ hrα hrβ hα0 hβ0 hα hβ hiα hiβ
      (by intro z hz hzc; rw [hαrange z hz, A.stable_kernel i (α z) hzc])
      (by intro z hz hzc; rw [hβrange z hz, A.unstable_kernel i (β z) hzc])
  exact ⟨r, r, e, i, hr, hrα', hr, hrβ', hsource, hx, he, hei, hspec⟩


end HolomorphicAnosov.Ghys
