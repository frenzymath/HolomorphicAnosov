import HolomorphicAnosov.Paper.Ghys.FlatProjectiveAtlas
import HolomorphicAnosov.Geometry.MobiusGroupContinuousG9
import Mathlib.Topology.FiberBundle.Basic

/-! Projective-frame evaluation is continuous and agrees with evaluation in every local
trivialization. (Thurston, §3.5, pp.34–35; §4.8, p.63) -/

open Set Filter Topology _root_.Topology

namespace HolomorphicAnosov.Ghys

/-- If Möbius transformations act continuously on `OnePoint ℂ`, projective-frame evaluation is
continuous and independent of the local chart label. (Thurston, §3.5, pp.34–35; §4.8, p.63) -/
theorem flatProjectiveFrameEvaluation
    {X L ι : Type*} [TopologicalSpace X] [TopologicalSpace L]
    (A : FlatProjectiveAtlas X L ι) (Z : FiberBundleCore ι X MobiusGroup)
    (hbase : Z.baseSet = fun i ↦ (A.chart i).source)
    (hindex : Z.indexAt = A.indexAt)
    (hchange : Z.coordChange = fun i j x g ↦ g * (A.transition i j x)⁻¹)
    (hact : ∀ g : MobiusGroup, Continuous g.apply) :
    let ev : Z.TotalSpace → OnePoint ℂ :=
      fun p ↦ p.2.apply ((A.chart (A.indexAt p.1) p.1).2 : OnePoint ℂ)
    Continuous ev ∧ ∀ (i : ι) (p : Z.TotalSpace), p.1 ∈ (A.chart i).source →
      ev p = ((Z.localTriv i p).2).apply ((A.chart i p.1).2 : OnePoint ℂ) := by
  let ev : Z.TotalSpace → OnePoint ℂ :=
    fun p ↦ p.2.apply ((A.chart (A.indexAt p.1) p.1).2 : OnePoint ℂ)
  have hform : ∀ (i : ι) (p : Z.TotalSpace), p.1 ∈ (A.chart i).source →
      ev p = ((Z.localTriv i p).2).apply ((A.chart i p.1).2 : OnePoint ℂ) := by
    intro i p hp
    dsimp only [ev]
    rw [Z.localTriv_apply, hchange, hindex]
    rw [A.transition_agrees (A.indexAt p.1) i p.1 ⟨A.mem_source p.1, hp⟩]
    change p.2.val _ = (p.2.val * (A.transition (A.indexAt p.1) i p.1).val⁻¹)
      ((A.transition (A.indexAt p.1) i p.1).val _)
    simp
  refine ⟨continuous_iff_continuousAt.mpr ?_, hform⟩
  intro p
  let i := A.indexAt p.1
  have hp : p.1 ∈ (A.chart i).source := A.mem_source p.1
  have hmem : p ∈ (Z.localTriv i).source := by
    rw [(Z.localTriv i).mem_source, ← Z.baseSet_at, hbase]
    exact hp
  have hlabel : ContinuousAt (fun w : Z.TotalSpace ↦ (Z.localTriv i w).2) p :=
    ((Z.localTriv i).toOpenPartialHomeomorph.continuousAt hmem).snd
  have hfixed : ∀ᶠ w in 𝓝 p, (Z.localTriv i w).2 = (Z.localTriv i p).2 := by
    exact hlabel.eventually ((isOpen_discrete {(Z.localTriv i p).2}).mem_nhds
      (mem_singleton _))
  have hsource : ∀ᶠ w : Z.TotalSpace in 𝓝 p, w.1 ∈ (A.chart i).source :=
    Z.continuous_proj.continuousAt ((A.chart i).open_source.mem_nhds hp)
  have hc : ContinuousAt
      (fun w : Z.TotalSpace ↦ ((Z.localTriv i p).2).apply
        ((A.chart i w.1).2 : OnePoint ℂ)) p :=
    (hact _).continuousAt.comp
      (OnePoint.continuous_coe.continuousAt.comp
        (((A.chart i).continuousAt hp).comp Z.continuous_proj.continuousAt).snd)
  apply hc.congr_of_eventuallyEq
  filter_upwards [hfixed, hsource] with w hw hs
  exact (hform i w hs).trans (by rw [hw])

end HolomorphicAnosov.Ghys
