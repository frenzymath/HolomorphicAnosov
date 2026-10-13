import Mathlib.Topology.Homotopy.Lifting

noncomputable section
open scoped Topology
open Filter Set _root_.Topology

universe u v w
namespace HolomorphicAnosov.Ghys

/-- A pointed lift of an injective intrinsic inclusion is injective, and its marked point is uniquely determined by the projected point. (Hatcher, Prop. 1.33) -/
theorem injective_pointed_leaf_lift
    {L E M : Type*} [TopologicalSpace L] [TopologicalSpace E] [TopologicalSpace M]
    [SimplyConnectedSpace L] [LocallyPathConnectedSpace L]
    {p : E → M} (hp : IsCoveringMap p) (inc : C(L, M))
    (hi : Function.Injective inc) (x : L) (e : E) (hx : p e = inc x) :
    ∃ lift : C(L, E), Function.Injective lift ∧
      (∀ z, p (lift z) = inc z) ∧ (∀ z, inc z = p e → lift z = e) ∧
      ∀ lift' : C(L, E), lift' x = e → (∀ z, p (lift' z) = inc z) → lift' = lift := by
  obtain ⟨lift, ⟨hpoint, hproj⟩, huniq⟩ := hp.existsUnique_continuousMap_lifts inc x e hx
  refine ⟨lift, ?_, congrFun hproj, ?_, ?_⟩
  · intro z w hzw
    apply hi
    exact (congrFun hproj z).symm.trans ((congrArg p hzw).trans (congrFun hproj w))
  · intro z hz
    have hz' : z = x := hi (hz.trans hx)
    simpa only [hz'] using hpoint
  · intro lift' hpoint' hproj'
    exact huniq lift' ⟨hpoint', funext hproj'⟩

end HolomorphicAnosov.Ghys

