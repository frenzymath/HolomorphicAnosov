import HolomorphicAnosov.Geometry.FlatProjectiveFrameCoverG9
import Mathlib.Topology.Homotopy.Lifting

noncomputable section
open Set Filter _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- A covering projection from a simply connected, locally path connected space lifts
to the effective Möbius frame cover. -/
theorem transverse_mobius_frame_lift
    {M Y L ι : Type*} [TopologicalSpace M] [TopologicalSpace Y] [TopologicalSpace L]
    [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y]
    (A : FlatProjectiveAtlas M L ι) (p : Y → M) (hp : IsCoveringMap p) :
    ∃ Z : FiberBundleCore ι M MobiusGroup,
      Z.baseSet = (fun i ↦ (A.chart i).source) ∧
      Z.indexAt = A.indexAt ∧
      Z.coordChange = (fun i j x g ↦ g * (A.transition i j x)⁻¹) ∧
      IsCoveringMap Z.proj ∧
      ∃ s : C(Y, Z.TotalSpace),
        (∀ y, (s y).proj = p y) := by
  obtain ⟨Z, hbase, hindex, hchange, hcover⟩ := flatProjectiveFrameCover A
  let : Nonempty MobiusGroup := ⟨1⟩
  let y₀ : Y := Classical.choice inferInstance
  let e₀ : Z.TotalSpace := ⟨p y₀, (1 : MobiusGroup)⟩
  obtain ⟨s, hs, _⟩ := hcover.existsUnique_continuousMap_lifts
    ⟨p, hp.continuous⟩ y₀ e₀ rfl
  refine ⟨Z, hbase, hindex, hchange, hcover, s, ?_⟩
  intro y
  exact congrFun hs.2 y

end HolomorphicAnosov.Ghys
