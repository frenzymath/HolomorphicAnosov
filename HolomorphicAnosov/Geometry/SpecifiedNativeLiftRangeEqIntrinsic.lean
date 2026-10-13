import HolomorphicAnosov.SurfaceTorusSupport.ReverseDevelopingLeafRangeOfPathBridge

/-! This file identifies the range of a specified lift of a path-connected intrinsic leaf (Hatcher, Prop. 1.34). -/

namespace HolomorphicAnosov

/-- A continuous lift from a path-connected leaf has exactly the pointed intrinsic path-lift range (Hatcher, Prop. 1.34). -/
theorem specified_native_lift_range_eq_intrinsic
    {S U L : Type*} [TopologicalSpace S] [TopologicalSpace U] [TopologicalSpace L]
    [PathConnectedSpace L] (π : U → S) (j : L → S) (lift : L → U)
    (hπ : IsCoveringMap π) (hlift : Continuous lift)
    (hproj : ∀ z, π (lift z) = j z) (a : L) (x : U) (hpoint : lift a = x) :
    Set.range lift = liftedIntrinsicLeafRange π j a x := by
  apply Set.Subset.antisymm
  · rintro _ ⟨b, rfl⟩
    subst x
    let γ := PathConnectedSpace.somePath a b
    exact ⟨b, γ, γ.map hlift, fun t ↦ hproj (γ t)⟩
  · exact reverse_developing_leaf_range_of_path_bridge π j lift hπ hlift hproj
      a x hpoint _ (fun _ hz ↦ hz)


end HolomorphicAnosov
