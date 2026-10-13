import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveFrameCoverG7
import Mathlib.Topology.Homotopy.Lifting

/-! A simply connected manifold cover admits a lift to the ordered frame covering after a choice of
initial frame. -/
noncomputable section
open Set _root_.Topology
open scoped ContDiff Bundle
namespace HolomorphicAnosov.Ghys
universe u v w
attribute [local instance] complex_isManifold_real

theorem ordered_projective_frame_section
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    (Z : FiberBundleCore A.index S OrderedProjectiveFrameGroup)
    (hZcover : IsCoveringMap Z.proj)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U] (p : U → S)
    (hp : IsCoveringMap p) (hsimply : SimplyConnectedSpace U) :
    ∃ s : C(U, Z.TotalSpace), ∀ u, (s u).proj = p u := by
  let : SimplyConnectedSpace U := hsimply
  let : LocallyPathConnectedSpace U :=
    ChartedSpace.locallyPathConnectedSpace (ComplexModel 2) U
  let u₀ : U := Classical.choice (inferInstance : Nonempty U)
  let e₀ : Z.TotalSpace := ⟨p u₀, (1 : OrderedProjectiveFrameGroup)⟩
  have he₀ : e₀.proj = p u₀ := rfl
  obtain ⟨s, hs₀, _⟩ := hZcover.existsUnique_continuousMap_lifts
    ⟨p, hp.continuous⟩ u₀ e₀ he₀
  refine ⟨s, ?_⟩
  intro u
  exact congrFun hs₀.2 u

end HolomorphicAnosov.Ghys
