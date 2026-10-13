import HolomorphicAnosov.Geometry.FlatProjectiveFrameEvaluationG9
import HolomorphicAnosov.Geometry.TransverseMobiusFrameLift
import HolomorphicAnosov.Geometry.ComplexMobiusOnePointBridge
import HolomorphicAnosov.Geometry.MobiusGroupContinuousG9
import Mathlib.Topology.Homotopy.Lifting

noncomputable section
open Set Filter _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- A section of the frame cover can be normalized to a prescribed Möbius germ
at a chosen point. -/
theorem transverse_mobius_initial_section
    {M Y L ι : Type*} [TopologicalSpace M] [TopologicalSpace Y] [TopologicalSpace L]
    [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y]
    (A : FlatProjectiveAtlas M L ι)
    (Z : FiberBundleCore ι M MobiusGroup)
    (hbase : Z.baseSet = fun i ↦ (A.chart i).source)
    (hindex : Z.indexAt = A.indexAt)
    (hchange : Z.coordChange = fun i j x g ↦ g * (A.transition i j x)⁻¹)
    (hcover : IsCoveringMap Z.proj) (p : Y → M) (hp : IsCoveringMap p)
    (y₀ : Y) (i₀ : ι) (g₀ : ComplexMobiusTransformation)
    (hi₀ : p y₀ ∈ (A.chart i₀).source) :
    ∃ s : C(Y, Z.TotalSpace),
      s y₀ = ⟨p y₀,
        complexMobiusToMobiusGroup g₀ * A.transition (A.indexAt (p y₀)) i₀ (p y₀)⟩ ∧
      (∀ y, (s y).proj = p y) ∧
      let ev : Z.TotalSpace → OnePoint ℂ :=
        fun z ↦ z.2.apply ((A.chart (A.indexAt z.1) z.1).2 : OnePoint ℂ)
      ev (s y₀) =
        (complexMobiusToMobiusGroup g₀).apply
          ((A.chart i₀ (p y₀)).2 : OnePoint ℂ) := by
  let e₀ : Z.TotalSpace := ⟨p y₀,
    complexMobiusToMobiusGroup g₀ * A.transition (A.indexAt (p y₀)) i₀ (p y₀)⟩
  have he₀ : e₀.proj = p y₀ := rfl
  obtain ⟨s, hs₀, hsproj⟩ := hcover.existsUnique_continuousMap_lifts
    ⟨p, hp.continuous⟩ y₀ e₀ he₀
  have hev := (flatProjectiveFrameEvaluation A Z hbase hindex hchange
    (fun g ↦ mobiusGroup_continuous_apply g)).2
  have hev₀ := hev i₀ e₀ hi₀
  refine ⟨s, hs₀.1, ?_, ?_⟩
  · intro y
    exact congrFun hs₀.2 y
  · dsimp only [e₀]
    rw [hs₀.1]
    calc
      _ = (Z.localTriv i₀ e₀).2.apply
          ((A.chart i₀ e₀.proj).2 : OnePoint ℂ) := hev₀
      _ = (complexMobiusToMobiusGroup g₀).apply
          ((A.chart i₀ (p y₀)).2 : OnePoint ℂ) := by
        rw [Z.localTriv_apply, hchange]
        rw [A.transition_agrees (A.indexAt (p y₀)) i₀ (p y₀)
          ⟨A.mem_source _, hi₀⟩]
        change (complexMobiusToMobiusGroup g₀ *
          A.transition (A.indexAt (p y₀)) i₀ (p y₀)).apply _ = _
        rw [hindex]
        change (complexMobiusToMobiusGroup g₀).val
            ((A.transition (A.indexAt (p y₀)) i₀ (p y₀)).val
              ((A.transition (A.indexAt (p y₀)) i₀ (p y₀)).val⁻¹
                ((A.transition (A.indexAt (p y₀)) i₀ (p y₀)).val
                  ((A.chart (A.indexAt (p y₀)) (p y₀)).2 : OnePoint ℂ)))) = _
        have hcancel : ∀ z : OnePoint ℂ,
            (A.transition (A.indexAt (p y₀)) i₀ (p y₀)).val
                ((A.transition (A.indexAt (p y₀)) i₀ (p y₀)).val⁻¹ z) = z := by
          intro z
          exact (A.transition (A.indexAt (p y₀)) i₀ (p y₀)).val.right_inv z
        rw [hcancel]
        rfl

end HolomorphicAnosov.Ghys
