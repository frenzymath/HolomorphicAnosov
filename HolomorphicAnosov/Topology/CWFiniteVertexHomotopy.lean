import HolomorphicAnosov.Topology.FiniteVertexHomotopyRelativeClosed
import HolomorphicAnosov.Topology.CWComplex.HomotopyExtension

noncomputable section
universe u v
namespace HolomorphicAnosov.Topology

/-- Move a finite family of vertices in a CW subcomplex to a basepoint while
fixing its complementary closed piece, and extend that homotopy to the whole
CW complex. Source: Hatcher, Algebraic Topology, proof of Theorem 2A.1 p.167
and Proposition 0.16 p.15. Closed pasting constructs the prescribed homotopy
on the subcomplex; the CW-pair homotopy extension theorem extends it without
changing its values there. The CW complex need not be connected, and no
separation assumption on the target is required. Its path-connectedness
supplies the vertex tracks. -/
theorem cw_finiteVertex_homotopy
    {Z : Type u} {X : Type v} [TopologicalSpace Z] [T2Space Z]
    [TopologicalSpace X] [PathConnectedSpace X]
    [_root_.Topology.CWComplex (Set.univ : Set Z)]
    (B : _root_.Topology.RelCWComplex.Subcomplex (Set.univ : Set Z))
    (V E : Set (B : Set Z)) (hV : V.Finite) (hE : IsClosed E)
    (hcover : ∀ z : (B : Set Z), z ∈ V ∨ z ∈ E)
    (f : C(Z, X)) (x : X) (hfixed : ∀ z ∈ V ∩ E, f z.val = x) :
    ∃ H : C(unitInterval × Z, X),
      (∀ z, H (0, z) = f z) ∧
      (∀ t (z : (B : Set Z)), z ∈ E → H (t, z.val) = f z.val) ∧
      (∀ z : (B : Set Z), z ∈ V → H (1, z.val) = x) := by
  let fB : C((B : Set Z), X) := f.comp ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨h, hzero, hEfixed, hVone⟩ :=
    finiteVertex_homotopy_relative_closed V E hV hE hcover fB x hfixed
  obtain ⟨H, hH0, hHB, _⟩ := HolomorphicAnosov.cw_pair_homotopy_extension B f h hzero
  refine ⟨H, hH0, ?_, ?_⟩
  · intro t z hz
    rw [hHB t z]
    exact hEfixed t z hz
  · intro z hz
    rw [hHB 1 z]
    exact hVone z hz

end HolomorphicAnosov.Topology
