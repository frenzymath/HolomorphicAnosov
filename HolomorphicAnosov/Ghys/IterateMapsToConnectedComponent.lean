import HolomorphicAnosov.Ghys.DisconnectedComponentResidues

open Set

namespace HolomorphicAnosov.Ghys

/-- A component-preserving iterate of a homeomorphism maps each connected component to itself in both forward and inverse time. (Ghys, Prop. 3.1) -/
theorem iterate_mapsTo_connectedComponent
    {M : Type*} [TopologicalSpace M] [LocallyConnectedSpace M]
    (f : M ≃ₜ M) (N : ℕ)
    (hcomponent : ∀ x : M,
      connectedComponent ((f : M → M)^[N] x) = connectedComponent x)
    (x : M) :
    MapsTo ((f : M → M)^[N]) (connectedComponent x) (connectedComponent x) ∧
      MapsTo ((f.symm : M → M)^[N]) (connectedComponent x) (connectedComponent x) := by
  constructor
  · intro y hy
    have hyx : connectedComponent y = connectedComponent x :=
      (connectedComponent_eq hy).symm
    have hz : ((f : M → M)^[N]) y ∈ connectedComponent y := by
      rw [← hcomponent y]
      exact mem_connectedComponent
    exact hyx ▸ hz
  · intro y hy
    let z := ((f.symm : M → M)^[N]) y
    have hiter : ((f : M → M)^[N]) z = y := by
      simpa [z] using (Function.RightInverse.iterate f.right_inv N y)
    have hcompz : connectedComponent y = connectedComponent z := by
      rw [← hiter]
      exact hcomponent z
    have hyx : connectedComponent y = connectedComponent x :=
      (connectedComponent_eq hy).symm
    have hzy : connectedComponent z = connectedComponent x :=
      hcompz.symm.trans hyx
    exact hzy ▸ mem_connectedComponent

end HolomorphicAnosov.Ghys

