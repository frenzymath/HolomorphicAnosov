import HolomorphicAnosov.Geometry.CompactParametricTubeInjectivityG18
import HolomorphicAnosov.Analysis.ParametricInverseSpatialRegularityG18
import HolomorphicAnosov.Geometry.PlaqueMetricNormalProjectionG18
import Mathlib.Analysis.Normed.Operator.Prod

noncomputable section
namespace HolomorphicAnosov
open Set Filter
open scoped _root_.Topology

/-- A C¹ plaque family, a C¹ moving normal frame, and a smooth local addition determine C¹ inverse
tube charts on a common receiving neighborhood. The charts and their spatial derivatives vary
continuously with the parameter. -/
theorem parametric_plaque_tube_inverse_g18
    {P V K E : Type*} [TopologicalSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : P → V → E) (D : P × V → V →L[ℝ] E)
    (N : P × V → K →L[ℝ] E) (DN : P × V → V →L[ℝ] K →L[ℝ] E)
    (Ω : Set (P × V)) (hΩ : IsOpen Ω) (p₀ : P) (hp₀ : (p₀,0) ∈ Ω)
    (hq : ContinuousOn (fun z : P × V ↦ q z.1 z.2) Ω)
    (hD : ContinuousOn D Ω) (hN : ContinuousOn N Ω) (hDN : ContinuousOn DN Ω)
    (hd : ∀ z ∈ Ω, HasFDerivAt (q z.1) (D z) z.2)
    (hn : ∀ z ∈ Ω, HasFDerivAt (fun v ↦ N (z.1,v)) (DN z) z.2)
    (a : E × E → E) (U : Set (E × E)) (hU : IsOpen U)
    (ha : ContDiffOn ℝ 1 a U) (hu₀ : (q p₀ 0,0) ∈ U)
    (ha₀ : HasFDerivAt a (ContinuousLinearMap.fst ℝ E E +
      ContinuousLinearMap.snd ℝ E E) (q p₀ 0,0))
    (A : (V × K) ≃L[ℝ] E)
    (hA : (D (p₀,0)).coprod (N (p₀,0)) = A.toContinuousLinearMap) :
    ∃ Q : TopologicalSpace.Opens P, ∃ hpQ : p₀ ∈ Q,
      ∃ W : Set E, IsOpen W ∧ a (q p₀ 0,0) ∈ W ∧
      ∃ e : Q → OpenPartialHomeomorph (V × K) E,
        (∀ p : Q, (e p : V × K → E) = (fun z ↦ a (q p.1 z.1,N (p.1,z.1) z.2)) ∧
          (e p).target = W ∧ ContDiffOn ℝ 1 (e p) (e p).source ∧
          ContDiffOn ℝ 1 (e p).symm (e p).target ∧
          ∀ z ∈ (e p).source, (p.1,z.1) ∈ Ω ∧ (q p.1 z.1,N (p.1,z.1) z.2) ∈ U) ∧
        ContinuousOn (fun z : Q × E ↦ (e z.1).symm z.2) (univ ×ˢ W) ∧
        ContinuousOn (fun z : Q × E ↦ fderiv ℝ (e z.1).symm z.2) (univ ×ˢ W) ∧ 0 ∈ (e ⟨p₀,hpQ⟩).source ∧
        IsOpen {z : Q × (V × K) | z.2 ∈ (e z.1).source} := by
  let j : P × (V × K) → P × V := fun z ↦ (z.1,z.2.1)
  have hj : Continuous j := continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  let S₀ := j ⁻¹' Ω
  have hS₀ : IsOpen S₀ := hΩ.preimage hj
  have hmap : MapsTo j S₀ Ω := fun _ hz ↦ hz
  let G : P × (V × K) → E × E := fun z ↦ (q z.1 z.2.1,N (z.1,z.2.1) z.2.2)
  have hGc : ContinuousOn G S₀ :=
    (hq.comp hj.continuousOn hmap).prodMk ((hN.comp hj.continuousOn hmap).clm_apply
      (continuous_snd.comp continuous_snd).continuousOn)
  let S := S₀ ∩ G ⁻¹' U
  have hS : IsOpen S := hGc.isOpen_inter_preimage hS₀ hU
  have hpS : (p₀,(0 : V × K)) ∈ S := by
    refine ⟨hp₀,?_⟩
    simpa only [G,Prod.fst_zero,Prod.snd_zero,map_zero,Set.mem_preimage] using hu₀
  let T : P → V × K → E := fun p z ↦ a (q p z.1,N (p,z.1) z.2)
  let Fst := ContinuousLinearMap.fst ℝ V K
  let Snd := ContinuousLinearMap.snd ℝ V K
  let B : P × (V × K) → (V × K) →L[ℝ] E × E := fun z ↦
    ((D (j z)).comp Fst).prod
      ((N (j z)).comp Snd + ((DN (j z)).comp Fst).flip z.2.2)
  let DT : P × (V × K) → (V × K) →L[ℝ] E := fun z ↦ (fderiv ℝ a (G z)).comp (B z)
  have hBc : ContinuousOn B S₀ := by
    have hD' := (hD.comp hj.continuousOn hmap).clm_comp (continuousOn_const (c := Fst))
    have hN' := (hN.comp hj.continuousOn hmap).clm_comp (continuousOn_const (c := Snd))
    let flip : ((V × K) →L[ℝ] K →L[ℝ] E) →L[ℝ] (K →L[ℝ] (V × K) →L[ℝ] E) :=
      (ContinuousLinearMap.flipₗᵢ ℝ (V × K) K E).toContinuousLinearEquiv.toContinuousLinearMap
    have hDN' := flip.continuous.comp_continuousOn
      ((hDN.comp hj.continuousOn hmap).clm_comp (continuousOn_const (c := Fst)))
    exact (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := V × K) (F := E) (G := E) ℝ).continuous.comp_continuousOn
      (hD'.prodMk (hN'.add (hDN'.clm_apply
        (continuous_snd.comp continuous_snd).continuousOn)))
  have hTc : ContinuousOn (fun z : P × (V × K) ↦ T z.1 z.2) S :=
    ha.continuousOn.comp (hGc.mono inter_subset_left) (fun _ hz ↦ hz.2)
  have hDTc : ContinuousOn DT S :=
    ((ha.continuousOn_fderiv_of_isOpen hU le_rfl).comp
      (hGc.mono inter_subset_left) (fun _ hz ↦ hz.2)).clm_comp (hBc.mono inter_subset_left)
  have hTd (z : P × (V × K)) (hz : z ∈ S) : HasFDerivAt (T z.1) (DT z) z.2 := by
    have hf : HasFDerivAt (Prod.fst : V × K → V) Fst z.2 := hasFDerivAt_fst
    have hs : HasFDerivAt (Prod.snd : V × K → K) Snd z.2 := hasFDerivAt_snd
    have hq' := (hd (j z) hz.1).comp z.2 hf
    have hn' := ((hn (j z) hz.1).comp z.2 hf).clm_apply hs
    exact ((ha.contDiffAt (hU.mem_nhds hz.2)).differentiableAt (by simp)).hasFDerivAt.comp
      z.2 (hq'.prodMk hn')
  have hDT₀ : DT (p₀,0) = A.toContinuousLinearMap := by
    simpa only [DT,B,G,j,Fst,Snd,Prod.fst_zero,Prod.snd_zero,map_zero,add_zero,
      ha₀.fderiv,ContinuousLinearMap.add_comp,ContinuousLinearMap.fst_comp_prod,
      ContinuousLinearMap.snd_comp_prod,ContinuousLinearMap.comp_fst_add_comp_snd] using hA
  obtain ⟨Q,hpQ,W,hW,hbW,e,he,hg,hgD,hcenter,hopen⟩ :=
    Analysis.parametric_c1_inverse_at_equiv_g18 T DT S hS p₀ hpS hTc hDTc hTd A hDT₀
  refine ⟨Q,hpQ,W,hW,?_,e,he,hg,hgD,hcenter,hopen⟩
  simpa only [T,Prod.fst_zero,Prod.snd_zero,map_zero] using hbW


/-- A plaque tube with jointly continuous spatial first derivative and invertible zero-section
derivative is injective on a uniform normal radius over an embedded compact plaque core for
nearby parameters. -/
theorem parametric_plaque_tube_uniform_injective_g18
    {P V K E : Type*} [TopologicalSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : P → V → E) (D : P × V → V →L[ℝ] E)
    (N : P × V → K →L[ℝ] E) (DN : P × V → V →L[ℝ] K →L[ℝ] E)
    (Ω : Set (P × V)) (hΩ : IsOpen Ω)
    (hq : ContinuousOn (fun z : P × V ↦ q z.1 z.2) Ω)
    (hD : ContinuousOn D Ω) (hN : ContinuousOn N Ω) (hDN : ContinuousOn DN Ω)
    (hd : ∀ z ∈ Ω, HasFDerivAt (q z.1) (D z) z.2)
    (hn : ∀ z ∈ Ω, HasFDerivAt (fun v ↦ N (z.1,v)) (DN z) z.2)
    (a : E × E → E) (U : Set (E × E)) (hU : IsOpen U)
    (ha : ContDiffOn ℝ 1 a U) (p₀ : P) (C : Set V) (hC : IsCompact C)
    (hCΩ : ∀ v ∈ C, (p₀,v) ∈ Ω) (hCU : ∀ v ∈ C, (q p₀ v,0) ∈ U)
    (hzero : ∀ v ∈ C, a (q p₀ v,0) = q p₀ v)
    (ha₀ : ∀ v ∈ C, HasFDerivAt a (ContinuousLinearMap.fst ℝ E E +
      ContinuousLinearMap.snd ℝ E E) (q p₀ v,0))
    (hinj : InjOn (q p₀) C)
    (hinvert : ∀ v ∈ C, ((D (p₀,v)).coprod (N (p₀,v))).IsInvertible) :
    ∃ Q ∈ 𝓝 p₀, ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ Q,
      InjOn (fun z : V × K ↦ a (q p z.1,N (p,z.1) z.2))
        (C ×ˢ Metric.ball (0 : K) ε) ∧
      ∀ z ∈ C ×ˢ Metric.ball (0 : K) ε,
        ((p,z.1) ∈ Ω ∧ (q p z.1,N (p,z.1) z.2) ∈ U) ∧
        (fderiv ℝ (fun w : V × K ↦ a (q p w.1,N (p,w.1) w.2)) z).IsInvertible := by
  let j : P × (V × K) → P × V := fun z ↦ (z.1,z.2.1)
  have hj : Continuous j := continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  let S₀ := j ⁻¹' Ω
  have hS₀ : IsOpen S₀ := hΩ.preimage hj
  have hmap : MapsTo j S₀ Ω := fun _ hz ↦ hz
  let G : P × (V × K) → E × E := fun z ↦ (q z.1 z.2.1,N (z.1,z.2.1) z.2.2)
  have hGc : ContinuousOn G S₀ :=
    (hq.comp hj.continuousOn hmap).prodMk ((hN.comp hj.continuousOn hmap).clm_apply
      (continuous_snd.comp continuous_snd).continuousOn)
  let S := S₀ ∩ G ⁻¹' U
  have hS : IsOpen S := hGc.isOpen_inter_preimage hS₀ hU
  let T : P → V × K → E := fun p z ↦ a (q p z.1,N (p,z.1) z.2)
  let Fst := ContinuousLinearMap.fst ℝ V K
  let Snd := ContinuousLinearMap.snd ℝ V K
  let B : P × (V × K) → (V × K) →L[ℝ] E × E := fun z ↦
    ((D (j z)).comp Fst).prod
      ((N (j z)).comp Snd + ((DN (j z)).comp Fst).flip z.2.2)
  let DT : P × (V × K) → (V × K) →L[ℝ] E := fun z ↦ (fderiv ℝ a (G z)).comp (B z)
  have hBc : ContinuousOn B S₀ := by
    have hD' := (hD.comp hj.continuousOn hmap).clm_comp (continuousOn_const (c := Fst))
    have hN' := (hN.comp hj.continuousOn hmap).clm_comp (continuousOn_const (c := Snd))
    let flip : ((V × K) →L[ℝ] K →L[ℝ] E) →L[ℝ] (K →L[ℝ] (V × K) →L[ℝ] E) :=
      (ContinuousLinearMap.flipₗᵢ ℝ (V × K) K E).toContinuousLinearEquiv.toContinuousLinearMap
    have hDN' := flip.continuous.comp_continuousOn
      ((hDN.comp hj.continuousOn hmap).clm_comp (continuousOn_const (c := Fst)))
    exact (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := V × K) (F := E) (G := E) ℝ).continuous.comp_continuousOn
      (hD'.prodMk (hN'.add (hDN'.clm_apply
        (continuous_snd.comp continuous_snd).continuousOn)))
  have hTc : ContinuousOn (fun z : P × (V × K) ↦ T z.1 z.2) S :=
    ha.continuousOn.comp (hGc.mono inter_subset_left) (fun _ hz ↦ hz.2)
  have hDTc : ContinuousOn DT S :=
    ((ha.continuousOn_fderiv_of_isOpen hU le_rfl).comp
      (hGc.mono inter_subset_left) (fun _ hz ↦ hz.2)).clm_comp (hBc.mono inter_subset_left)
  have hTd (z : P × (V × K)) (hz : z ∈ S) : HasFDerivAt (T z.1) (DT z) z.2 := by
    have hf : HasFDerivAt (Prod.fst : V × K → V) Fst z.2 := hasFDerivAt_fst
    have hs : HasFDerivAt (Prod.snd : V × K → K) Snd z.2 := hasFDerivAt_snd
    have hq' := (hd (j z) hz.1).comp z.2 hf
    have hn' := ((hn (j z) hz.1).comp z.2 hf).clm_apply hs
    exact ((ha.contDiffAt (hU.mem_nhds hz.2)).differentiableAt (by simp)).hasFDerivAt.comp
      z.2 (hq'.prodMk hn')
  suffices hh : ∃ Q ∈ 𝓝 p₀, ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ Q,
      InjOn (T p) (C ×ˢ Metric.ball (0 : K) ε) ∧
      ∀ z ∈ C ×ˢ Metric.ball (0 : K) ε, (p,z) ∈ S ∧ (DT (p,z)).IsInvertible by
    obtain ⟨Q,hQ,ε,hε,hh⟩ := hh
    refine ⟨Q,hQ,ε,hε,?_⟩
    intro p hp
    refine ⟨(hh p hp).1,?_⟩
    intro z hz
    obtain ⟨hs,hi⟩ := (hh p hp).2 z hz
    refine ⟨hs,?_⟩
    change (fderiv ℝ (T p) z).IsInvertible
    rw [(hTd (p,z) hs).fderiv]
    exact hi
  apply compact_parametric_c1_tube_regular_g18 T DT S hS p₀ C hC
  · intro v hv
    refine ⟨hCΩ v hv,?_⟩
    simpa only [G,mem_preimage,map_zero] using hCU v hv
  · exact hTc
  · exact hDTc
  · exact hTd
  · intro v hv w hw heq
    apply hinj hv hw
    simpa only [T,map_zero,hzero v hv,hzero w hw] using heq
  · intro v hv
    have hDTzero : DT (p₀,(v,0)) = (D (p₀,v)).coprod (N (p₀,v)) := by
      simp only [DT,B,G,j,Fst,Snd,map_zero,add_zero,(ha₀ v hv).fderiv,
        ContinuousLinearMap.add_comp,ContinuousLinearMap.fst_comp_prod,
        ContinuousLinearMap.snd_comp_prod,ContinuousLinearMap.comp_fst_add_comp_snd]
    rw [hDTzero]
    exact hinvert v hv

end HolomorphicAnosov

