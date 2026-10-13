import HolomorphicAnosov.Ghys.IterateMapsToConnectedComponent
import HolomorphicAnosov.Geometry.RestrictedOpenDiffeomorph
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Manifold.Diffeomorph.RealIterate

open Set
open scoped ContDiff Manifold Topology _root_.Topology
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real

/-- Each connected component is an open compact complex submanifold, and a positive iterate
preserving it restricts to a smooth diffeomorphism of that component. (Lee, Prop. 1.8(a)–(d),
pp.9–10) -/
theorem connected_component_restricted_iterate
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [LocallyConnectedSpace M] (f : Biholomorph d d M M) (N : ℕ)
    (hcomponent : ∀ y : M,
      connectedComponent ((f : M → M)^[N] y) = connectedComponent y)
    (x : M) :
    ∃ K : TopologicalSpace.Opens M,
      (K : Set M) = connectedComponent x ∧
      ∃ (_ : IsCompactComplexManifold d K),
        Nonempty (Diffeomorph (realModel d) (realModel d) K K ∞) := by
  let K : TopologicalSpace.Opens M := ⟨connectedComponent x, isOpen_connectedComponent⟩
  have hx : x ∈ (K : Set M) := mem_connectedComponent
  have hnonempty : Nonempty K := ⟨⟨x, hx⟩⟩
  have hcompact : IsCompact (K : Set M) := by
    change IsCompact (connectedComponent x)
    exact isClosed_connectedComponent.isCompact
  let : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  let : ConnectedSpace K := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let : T2Space K := inferInstance
  let : SecondCountableTopology K := inferInstance
  let : ChartedSpace (ComplexModel d) K := inferInstance
  let : IsManifold (complexModel d) ∞ K := inferInstance
  have hres := iterate_mapsTo_connectedComponent f.toHomeomorph N hcomponent x
  have hmap : MapsTo ((realIterate (realModel d) f.toReal N : M → M) : M → M)
      (K : Set M) (K : Set M) := by
    intro y hy
    exact hres.1 hy
  have hinv : MapsTo ((realIterate (realModel d) f.toReal N).symm : M → M)
      (K : Set M) (K : Set M) := by
    intro y hy
    exact hres.2 hy
  have hF := restricted_open_diffeomorph (realIterate (realModel d) f.toReal N) K hnonempty hmap hinv
  let : IsCompactComplexManifold d K := { }
  refine ⟨K, rfl, inferInstance, ⟨hF⟩⟩

end HolomorphicAnosov.Ghys
