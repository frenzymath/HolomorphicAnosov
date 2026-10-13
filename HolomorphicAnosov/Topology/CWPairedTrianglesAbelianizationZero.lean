import HolomorphicAnosov.Topology.CWVertexHomotopyFixedSimplexEdge
import HolomorphicAnosov.Topology.PairedContinuousTrianglesAbelianizationZero

noncomputable section
open CategoryTheory Convexity
open scoped Simplicial
universe u v
namespace HolomorphicAnosov.Topology

/-- A based loop realized as the distinguished boundary edge of a finite
signed triangle family in a CW complex has zero abelianization class.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.167 and Proposition
0.16 p.15. Move the finite zero-skeleton to the target basepoint by homotopy
extension while fixing the distinguished characteristic edge. Restriction of
the final map to the triangles has based vertices, unchanged paired edge
parameters and the original distinguished loop. The signed continuous
triangle cancellation theorem gives the asserted zero class. The CW complex
need not be connected and no target separation axiom is required. -/
theorem cw_pairedTriangles_abelianization_zero
    {Z : Type u} {X : Type v} [TopologicalSpace Z] [T2Space Z]
    [TopologicalSpace X] [PathConnectedSpace X]
    [_root_.Topology.CWComplex (Set.univ : Set Z)]
    [Finite (_root_.Topology.RelCWComplex.cell (Set.univ : Set Z) 0)]
    {x : X} (α : Path x x) (m : ℕ)
    (triangle : Fin m → C(StdSimplex ℝ (Fin 3), Z))
    (edge : Fin m × Fin 3 → C(StdSimplex ℝ (Fin 2), Z))
    (hface : ∀ i j t, triangle i (t.map j.succAbove) = edge (i, j) t)
    (hvertex : ∀ i j, triangle i (StdSimplex.single j) ∈
      (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set Z) 0 : Set Z))
    (ε : Fin m → ℤ) (d : Fin m × Fin 3)
    (pair : Fin m × Fin 3 → Fin m × Fin 3)
    (hpair : Function.Involutive pair) (hd : pair d = d)
    (hfree : ∀ o, o ≠ d → pair o ≠ o)
    (hsign : ∀ o, o ≠ d →
      ε (pair o).1 * (-1 : ℤ) ^ (pair o).2.val = -(ε o.1 * (-1 : ℤ) ^ o.2.val))
    (hedge : ∀ o, edge (pair o) = edge o)
    (hdpos : ε d.1 * (-1 : ℤ) ^ d.2.val = 1)
    (i : _root_.Topology.RelCWComplex.cell (Set.univ : Set Z) 1)
    (disk : StdSimplex ℝ (Fin 2) ≃ₜ Metric.closedBall (0 : Fin 1 → ℝ) 1)
    (hdisk : ∀ t, (disk t).val ∈ Metric.ball (0 : Fin 1 → ℝ) 1 ↔
      ∀ j, 0 < t.weights j)
    (he : ∀ t, edge d t = _root_.Topology.RelCWComplex.map 1 i (disk t).val)
    (B : _root_.Topology.RelCWComplex.Subcomplex (Set.univ : Set Z))
    (hB : (B : Set Z) =
      (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set Z) 0 : Set Z) ∪
      Set.range (edge d))
    (S : C(Z, X))
    (hdedge : ∀ t, S (edge d t) = α (StdSimplex.homeomorphI t)) :
    Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk α))) = 0 := by
  obtain ⟨H, _, hfixed, hvertices⟩ := cw_vertex_homotopy_fixed_simplex_edge
    i disk hdisk (edge d) he B hB S x
    (by simpa only [StdSimplex.homeomorphI_single_zero, Path.source] using
      hdedge (StdSimplex.single 0))
    (by simpa only [StdSimplex.homeomorphI_single_one, Path.target] using
      hdedge (StdSimplex.single 1))
  let f : C(Z, X) := H.comp ⟨fun z ↦ (1, z), continuous_const.prodMk continuous_id⟩
  apply pairedContinuousTriangles_abelianization_zero α m
    (fun j ↦ f.comp (triangle j)) (fun o ↦ f.comp (edge o))
    (fun j k t ↦ congrArg f (hface j k t))
    (fun j k ↦ hvertices _ (hvertex j k)) ε d pair hpair hd hfree hsign
    (fun o ↦ congrArg (fun e ↦ f.comp e) (hedge o)) hdpos
  apply ContinuousMap.ext
  intro t
  change H (1, edge d t) = α (StdSimplex.homeomorphI t)
  exact (hfixed 1 t).trans (hdedge t)

end HolomorphicAnosov.Topology
