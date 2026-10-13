import HolomorphicAnosov.Ghys.ComplexRestrictedOpenBiholomorph

/-! This file restricts a component-preserving iterate of a biholomorphism to each open connected
component as a complex diffeomorphism. (Ghys, Prop. 3.1, p.590; Lee, Prop. 1.8, pp.9–10) -/

open Set
open scoped ContDiff Manifold Topology _root_.Topology
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real

@[simp] theorem coe_complexDiffeomorphIterate_symm
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (n : ℕ) :
    ((complexDiffeomorphIterate f n).symm : M → M) =
      (f.symm : M → M)^[n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      apply funext
      intro x
      rw [complexDiffeomorphIterate]
      rw [Diffeomorph.symm_trans']
      rw [Diffeomorph.coe_trans]
      change (complexDiffeomorphIterate f n).symm (f.symm x) = _
      rw [Function.iterate_succ_apply]
      rw [ih]

/-- A component-preserving iterate restricts to a complex diffeomorphism on each nonempty connected
component subtype. -/
theorem connected_component_complex_restricted_iterate
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [LocallyConnectedSpace M] (f : Biholomorph d d M M) (N : ℕ)
    (hcomponent : ∀ y : M,
      connectedComponent ((f : M → M)^[N] y) = connectedComponent y)
    (x : M) :
    ∃ K : TopologicalSpace.Opens M,
      (K : Set M) = connectedComponent x ∧
      Nonempty (Biholomorph d d K K) := by
  let K : TopologicalSpace.Opens M := ⟨connectedComponent x, isOpen_connectedComponent⟩
  have hx : x ∈ (K : Set M) := mem_connectedComponent
  have hnonempty : Nonempty K := ⟨⟨x, hx⟩⟩
  let : ConnectedSpace K := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let : T2Space K := inferInstance
  let : SecondCountableTopology K := inferInstance
  let : ChartedSpace (ComplexModel d) K := inferInstance
  let : IsManifold (complexModel d) ∞ K := inferInstance
  have hres := iterate_mapsTo_connectedComponent f.toHomeomorph N hcomponent x
  have hmap : MapsTo ((f : M → M)^[N]) (K : Set M) (K : Set M) := by
    intro y hy
    exact hres.1 hy
  have hinv : MapsTo (((f.symm : M → M)^[N])) (K : Set M) (K : Set M) := by
    intro y hy
    exact hres.2 hy
  refine ⟨K, rfl, ⟨restricted_open_biholomorph (complexDiffeomorphIterate f N)
    K hnonempty (by simpa [coe_complexDiffeomorphIterate] using hmap)
    (by simpa [coe_complexDiffeomorphIterate_symm] using hinv)⟩⟩

end HolomorphicAnosov.Ghys
