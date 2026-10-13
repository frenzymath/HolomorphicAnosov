import HolomorphicAnosov.Geometry.FlatProjectiveFrameEvaluationG9
import HolomorphicAnosov.Geometry.MobiusGroupCarrierG9
import HolomorphicAnosov.Geometry.NativeProjectiveLineTopology

noncomputable section
open Set Filter _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- Evaluation of a continuous frame section has local Möbius coordinate expressions. -/
theorem transverse_mobius_section_local_form
    {M Y L ι : Type*} [TopologicalSpace M] [TopologicalSpace Y] [TopologicalSpace L]
    (A : FlatProjectiveAtlas M L ι)
    (Z : FiberBundleCore ι M MobiusGroup)
    (hbase : Z.baseSet = fun i ↦ (A.chart i).source)
    (hindex : Z.indexAt = A.indexAt)
    (hchange : Z.coordChange = fun i j x g ↦ g * (A.transition i j x)⁻¹)
    (p : Y → M) (hp : Continuous p)
    (s : C(Y, Z.TotalSpace)) (hsproj : ∀ y, (s y).proj = p y) :
    let ev : Z.TotalSpace → OnePoint ℂ :=
      fun z ↦ z.2.apply ((A.chart (A.indexAt z.1) z.1).2 : OnePoint ℂ)
    let D : C(Y, ComplexProjectiveLine) :=
      ⟨fun y ↦ (OnePoint.equivProjectivization ℂ) (ev (s y)), by
        exact NativeProjectiveTopology.continuous_onePoint_projectivization.comp
          ((flatProjectiveFrameEvaluation A Z hbase hindex hchange
            (fun g ↦ mobiusGroup_continuous_apply g)).1.comp s.continuous)⟩
    ∀ y, ∃ i, ∃ g : ComplexMobiusTransformation, ∃ U : Set Y,
      IsOpen U ∧ y ∈ U ∧ U ⊆ p ⁻¹' (A.chart i).source ∧
        EqOn D (fun w ↦ g.apply
          (complexProjectiveLineFinite ((A.chart i (p w)).2))) U := by
  let ev : Z.TotalSpace → OnePoint ℂ :=
    fun z ↦ z.2.apply ((A.chart (A.indexAt z.1) z.1).2 : OnePoint ℂ)
  let D : C(Y, ComplexProjectiveLine) :=
    ⟨fun y ↦ (OnePoint.equivProjectivization ℂ) (ev (s y)), by
      exact NativeProjectiveTopology.continuous_onePoint_projectivization.comp
        ((flatProjectiveFrameEvaluation A Z hbase hindex hchange
          (fun g ↦ mobiusGroup_continuous_apply g)).1.comp s.continuous)⟩
  change ∀ y, ∃ i, ∃ g : ComplexMobiusTransformation, ∃ U : Set Y,
    IsOpen U ∧ y ∈ U ∧ U ⊆ p ⁻¹' (A.chart i).source ∧
      EqOn D (fun w ↦ g.apply
        (complexProjectiveLineFinite ((A.chart i (p w)).2))) U
  intro y
  let i := A.indexAt (p y)
  have hpy : p y ∈ (A.chart i).source := A.mem_source (p y)
  have hsy : s y ∈ (Z.localTriv i).source := by
    rw [(Z.localTriv i).mem_source]
    rw [← Z.baseSet_at, hbase]
    simpa [hsproj y] using hpy
  let gM : MobiusGroup := (Z.localTriv i (s y)).2
  let g : ComplexMobiusTransformation := mobiusGroupToComplexMobius gM
  have hlabelAt : ContinuousAt (fun z : Z.TotalSpace ↦ (Z.localTriv i z).2) (s y) :=
    ((Z.localTriv i).toOpenPartialHomeomorph.continuousAt hsy).snd
  have hevlabel : ∀ᶠ z in 𝓝 (s y), (Z.localTriv i z).2 = gM :=
    hlabelAt.eventually ((isOpen_discrete {gM}).mem_nhds (mem_singleton _))
  obtain ⟨V, hVsub, hVo, hsyV⟩ := mem_nhds_iff.mp hevlabel
  let U : Set Y := p ⁻¹' (A.chart i).source ∩ s ⁻¹' V
  refine ⟨i, g, U, ?_, ?_, ?_, ?_⟩
  · exact hp.isOpen_preimage (A.chart i).source (A.chart i).open_source |>.inter
      (s.continuous.isOpen_preimage V hVo)
  · exact ⟨hpy, hsyV⟩
  · intro w hw
    exact hw.1
  · intro w hw
    have hsw : s w ∈ (Z.localTriv i).source := by
      rw [(Z.localTriv i).mem_source, ← Z.baseSet_at, hbase]
      simpa [hsproj w] using hw.1
    have hev := (flatProjectiveFrameEvaluation A Z hbase hindex hchange
      (fun g ↦ mobiusGroup_continuous_apply g)).2 i (s w) (hsproj w ▸ hw.1)
    have hlabel : (Z.localTriv i (s w)).2 = gM := hVsub hw.2
    change D w = _
    change (OnePoint.equivProjectivization ℂ) (ev (s w)) = _
    rw [show ev (s w) =
      ((Z.localTriv i (s w)).2).apply
        ((A.chart i (s w).proj).2 : OnePoint ℂ) from hev]
    rw [hlabel]
    have hfin : (complexProjectiveLineFinite ((A.chart i (s w).proj).2)) =
        (OnePoint.equivProjectivization ℂ)
          (((A.chart i (s w).proj).2 : OnePoint ℂ)) := by
      apply (OnePoint.equivProjectivization ℂ).symm.injective
      rw [complexProjectiveLineFinite_to_onePoint]
      exact (Equiv.symm_apply_apply _ _).symm
    have hmob := mobiusGroupToComplexMobius_apply gM
      (complexProjectiveLineFinite ((A.chart i (s w).proj).2))
    rw [complexProjectiveLineFinite_to_onePoint] at hmob
    rw [← hmob]
    change _ = g.apply (complexProjectiveLineFinite ((A.chart i (p w)).2))
    rw [← hsproj w, hfin]

/-- A frame section with prescribed label in an initial chart evaluates to that Möbius
coordinate on a neighborhood of the initial point. (Thurston, §3.5, pp. 34–35) -/
theorem transverse_mobius_section_initial_local_form
    {M Y L ι : Type*} [TopologicalSpace M] [TopologicalSpace Y] [TopologicalSpace L]
    (A : FlatProjectiveAtlas M L ι) (Z : FiberBundleCore ι M MobiusGroup)
    (hbase : Z.baseSet = fun i ↦ (A.chart i).source)
    (hindex : Z.indexAt = A.indexAt)
    (hchange : Z.coordChange = fun i j x g ↦ g * (A.transition i j x)⁻¹)
    (p : Y → M) (hp : Continuous p) (s : C(Y, Z.TotalSpace))
    (hsproj : ∀ y, (s y).proj = p y)
    (y₀ : Y) (i₀ : ι) (g₀ : ComplexMobiusTransformation)
    (hi₀ : p y₀ ∈ (A.chart i₀).source)
    (hslabel : (Z.localTriv i₀ (s y₀)).2 = complexMobiusToMobiusGroup g₀) :
    let ev : Z.TotalSpace → OnePoint ℂ :=
      fun z ↦ z.2.apply ((A.chart (A.indexAt z.1) z.1).2 : OnePoint ℂ)
    let D : C(Y, ComplexProjectiveLine) :=
      ⟨fun y ↦ (OnePoint.equivProjectivization ℂ) (ev (s y)), by
        exact NativeProjectiveTopology.continuous_onePoint_projectivization.comp
          ((flatProjectiveFrameEvaluation A Z hbase hindex hchange
            (fun g ↦ mobiusGroup_continuous_apply g)).1.comp s.continuous)⟩
    ∃ U : Set Y, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ p ⁻¹' (A.chart i₀).source ∧
      EqOn D (fun w ↦ g₀.apply (complexProjectiveLineFinite ((A.chart i₀ (p w)).2))) U := by
  let ev : Z.TotalSpace → OnePoint ℂ :=
    fun z ↦ z.2.apply ((A.chart (A.indexAt z.1) z.1).2 : OnePoint ℂ)
  let D : C(Y, ComplexProjectiveLine) :=
    ⟨fun y ↦ (OnePoint.equivProjectivization ℂ) (ev (s y)), by
      exact NativeProjectiveTopology.continuous_onePoint_projectivization.comp
        ((flatProjectiveFrameEvaluation A Z hbase hindex hchange
          (fun g ↦ mobiusGroup_continuous_apply g)).1.comp s.continuous)⟩
  have hsy : s y₀ ∈ (Z.localTriv i₀).source := by
    rw [(Z.localTriv i₀).mem_source, ← Z.baseSet_at, hbase]
    simpa [hsproj y₀] using hi₀
  have hlabelAt : ContinuousAt (fun z : Z.TotalSpace ↦ (Z.localTriv i₀ z).2) (s y₀) :=
    ((Z.localTriv i₀).toOpenPartialHomeomorph.continuousAt hsy).snd
  have hevlabel : ∀ᶠ z in 𝓝 (s y₀), (Z.localTriv i₀ z).2 = complexMobiusToMobiusGroup g₀ :=
    hlabelAt.eventually ((isOpen_discrete {complexMobiusToMobiusGroup g₀}).mem_nhds
      (show (Z.localTriv i₀ (s y₀)).2 ∈ {complexMobiusToMobiusGroup g₀} by simpa [hslabel]))
  obtain ⟨V, hVsub, hVo, hsyV⟩ := mem_nhds_iff.mp hevlabel
  let U : Set Y := p ⁻¹' (A.chart i₀).source ∩ s ⁻¹' V
  refine ⟨U, hp.isOpen_preimage _ (A.chart i₀).open_source |>.inter
      (s.continuous.isOpen_preimage V hVo), ⟨hi₀, hsyV⟩, ?_, ?_⟩
  · intro w hw
    exact hw.1
  · intro w hw
    have hsw : s w ∈ (Z.localTriv i₀).source := by
      rw [(Z.localTriv i₀).mem_source, ← Z.baseSet_at, hbase]
      simpa [hsproj w] using hw.1
    have hev := (flatProjectiveFrameEvaluation A Z hbase hindex hchange
      (fun g ↦ mobiusGroup_continuous_apply g)).2 i₀ (s w) (hsproj w ▸ hw.1)
    have hlabel : (Z.localTriv i₀ (s w)).2 = complexMobiusToMobiusGroup g₀ := hVsub hw.2
    change D w = _
    change (OnePoint.equivProjectivization ℂ) (ev (s w)) = _
    rw [show ev (s w) = ((Z.localTriv i₀ (s w)).2).apply
      ((A.chart i₀ (s w).proj).2 : OnePoint ℂ) from hev, hlabel]
    have hmob := mobiusGroupToComplexMobius_apply (complexMobiusToMobiusGroup g₀)
      (complexProjectiveLineFinite ((A.chart i₀ (s w).proj).2))
    rw [complexProjectiveLineFinite_to_onePoint] at hmob
    rw [← hmob]
    change _ = g₀.apply (complexProjectiveLineFinite ((A.chart i₀ (p w)).2))
    rw [hsproj w, mobiusGroupToComplexMobius_apply]
    apply (OnePoint.equivProjectivization ℂ).symm.injective
    rw [Equiv.symm_apply_apply, complexMobiusToMobiusGroup_intertwines]


end HolomorphicAnosov.Ghys
