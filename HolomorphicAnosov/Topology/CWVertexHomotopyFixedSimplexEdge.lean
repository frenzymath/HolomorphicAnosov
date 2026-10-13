import HolomorphicAnosov.Topology.CWSimplexEdgeVertexEndpoints
import HolomorphicAnosov.Topology.CWFiniteZeroSkeleton
import HolomorphicAnosov.Topology.CWFiniteVertexHomotopy
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

noncomputable section
open Convexity
universe u v
namespace HolomorphicAnosov.Topology

/-- A map on a CW complex can move every vertex to a chosen point while
fixing one characteristic edge whose two endpoint images are that point.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.167 and Proposition
0.16 p.15. The zero-skeleton is finite, the edge image is compact and closed,
and their union is the specified subcomplex. Its intersection with the edge
contains only endpoint images, where the map already equals the basepoint.
Prescribe paths to the basepoint at all other vertices and the constant
homotopy on the edge; finite closed pasting and CW homotopy extension produce
the asserted homotopy. The CW complex need not be connected, and the target
requires no separation condition. -/
theorem cw_vertex_homotopy_fixed_simplex_edge
    {Z : Type u} {X : Type v} [TopologicalSpace Z] [T2Space Z]
    [TopologicalSpace X] [PathConnectedSpace X]
    [_root_.Topology.CWComplex (Set.univ : Set Z)]
    [Finite (_root_.Topology.RelCWComplex.cell (Set.univ : Set Z) 0)]
    (i : _root_.Topology.RelCWComplex.cell (Set.univ : Set Z) 1)
    (disk : StdSimplex ℝ (Fin 2) ≃ₜ Metric.closedBall (0 : Fin 1 → ℝ) 1)
    (hdisk : ∀ t, (disk t).val ∈ Metric.ball (0 : Fin 1 → ℝ) 1 ↔
      ∀ j, 0 < t.weights j)
    (e : C(StdSimplex ℝ (Fin 2), Z))
    (he : ∀ t, e t = _root_.Topology.RelCWComplex.map 1 i (disk t).val)
    (B : _root_.Topology.RelCWComplex.Subcomplex (Set.univ : Set Z))
    (hB : (B : Set Z) =
      (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set Z) 0 : Set Z) ∪
      Set.range e)
    (f : C(Z, X)) (x : X)
    (hzero : f (e (StdSimplex.single 0)) = x)
    (hone : f (e (StdSimplex.single 1)) = x) :
    ∃ H : C(unitInterval × Z, X),
      (∀ z, H (0, z) = f z) ∧
      (∀ t s, H (t, e s) = f (e s)) ∧
      (∀ z ∈ (_root_.Topology.RelCWComplex.skeleton
        (Set.univ : Set Z) 0 : Set Z), H (1, z) = x) := by
  let V : Set (B : Set Z) := Subtype.val ⁻¹'
    (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set Z) 0 : Set Z)
  let E : Set (B : Set Z) := Subtype.val ⁻¹' Set.range e
  have hV : V.Finite := cw_finite_zero_skeleton.preimage Subtype.val_injective.injOn
  have hE : IsClosed E := by
    apply IsClosed.preimage continuous_subtype_val
    exact isCompact_range e.continuous |>.isClosed
  have hcover : ∀ z : (B : Set Z), z ∈ V ∨ z ∈ E := by
    intro z
    have hz : z.val ∈ (_root_.Topology.RelCWComplex.skeleton
        (Set.univ : Set Z) 0 : Set Z) ∪ Set.range e := by
      simpa only [hB] using z.property
    exact hz
  have hfixed : ∀ z ∈ V ∩ E, f z.val = x := by
    rintro z ⟨hzV, s, hs⟩
    have hsV : e s ∈ (_root_.Topology.RelCWComplex.skeleton
        (Set.univ : Set Z) 0 : Set Z) := hs.symm ▸ hzV
    rcases cw_simplexEdge_vertex_endpoints i disk hdisk e he s hsV with h | h
    · simpa only [← hs, h] using hzero
    · simpa only [← hs, h] using hone
  obtain ⟨H, hH0, hHE, hHV⟩ := cw_finiteVertex_homotopy B V E hV hE hcover f x hfixed
  refine ⟨H, hH0, ?_, ?_⟩
  · intro t s
    have hmem : e s ∈ (B : Set Z) := by rw [hB]; exact Or.inr ⟨s, rfl⟩
    exact hHE t ⟨e s, hmem⟩ ⟨s, rfl⟩
  · intro z hz
    have hmem : z ∈ (B : Set Z) := by rw [hB]; exact Or.inl hz
    exact hHV ⟨z, hmem⟩ hz

end HolomorphicAnosov.Topology
