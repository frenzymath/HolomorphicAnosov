import Init
import HolomorphicAnosov.Topology.CWPairedTrianglesAbelianizationZero
import HolomorphicAnosov.Topology.DegreeOneHurewiczHom
import HolomorphicAnosov.Topology.LoopSingularClassEqZero
import HolomorphicAnosov.Topology.SingularTwoChainRelativeTriangleCWRealization
import HolomorphicAnosov.Topology.PairedQuotientFacesEq
import HolomorphicAnosov.Topology.PathSingularChain
import HolomorphicAnosov.Topology.DegreeOneHurewiczFunction
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Finite

noncomputable section
open CategoryTheory Convexity HolomorphicAnosov.RelativeTriangleRealization
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- The degree-one Hurewicz kernel is the commutator subgroup.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof pp.167–168.
Every commutator maps to the identity because the homology codomain is abelian.
For the reverse inclusion represent a kernel element by a based loop. Its
native homology class is zero, so the cycle-class zero criterion supplies an
actual singular two-chain with that loop as boundary. Realize the signed
triangle occurrences as a finite relative triangle CW complex with paired
parametrized edges and one distinguished edge representing the loop.

Keep the distinguished edge fixed and move every other vertex to the chosen
basepoint along a connecting path. The initial values agree at all vertices
of the distinguished edge, so this defines a homotopy on the subcomplex made
of the vertices and that edge. CW-pair homotopy extension extends the homotopy
to the whole finite triangle complex. At time one every triangle edge is a
based loop. Paired edge occurrences still have identical parameterizations
because they descend from the same edge of the quotient, while the distinguished
edge is the original loop throughout.

In the fundamental group's abelianization, paired signed edges cancel.
Consequently the original loop class equals the signed sum of triangle
boundary loop classes. Each such boundary is nullhomotopic: contract the
boundary loop linearly inside its standard convex triangle to its first
vertex, and compose with the triangle map. The base vertex stays fixed,
so this is a based nullhomotopy. Thus every triangle boundary has zero
abelianization class and so does the original loop. The kernel of the
canonical abelianization map is exactly the commutator subgroup, giving the
reverse inclusion and hence equality. This uses only path-connectedness of
the original space; the auxiliary finite complex is Hausdorff, not a replacement
or separation hypothesis on the original space. -/
theorem degreeOneHurewicz_kernel {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) :
    (degreeOneHurewicz x).ker = commutator (FundamentalGroup X x) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨α, rfl⟩ := Quotient.exists_rep a
    have hz : loopSingularClass α = 0 := by
      change Multiplicative.ofAdd (loopSingularClass α) = 1 at ha
      exact ha
    obtain ⟨c, hc⟩ := (loopSingularClass_eq_zero_iff α).mp hz
    let f := TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋1⦌)
      (pathSingularSimplex α)
    have hf0 : f (StdSimplex.single 0) = x := by
      change α (StdSimplex.homeomorphI (StdSimplex.single 0)) = x
      simp
    have hf1 : f (StdSimplex.single 1) = x := by
      change α (StdSimplex.homeomorphI (StdSimplex.single 1)) = x
      simp
    have hcf : (((TopCat.toSSet.obj (TopCat.of X)).chainComplex
        (ModuleCat.of ℤ (ULift.{u} ℤ))).d 2 1) c = generator (TopCat.of X) 1 f := by
      simpa only [generator, f, Equiv.symm_apply_apply, pathSingularChain,
        show ULift.up (1 : ℤ) = (1 : ULift.{u} ℤ) from rfl] using hc
    obtain ⟨m, σ, ε, d, pair, _, _, hinv, hd, hfree, hsign, _, hpos, _, hCW,
      S, _, hS⟩ := singularTwoChainRelativeTriangleCWRealization (TopCat.of X)
        f (hf0.trans hf1.symm) c hcf
    obtain ⟨hT2, cw, hCW⟩ := hCW
    let := hT2
    let := cw
    obtain ⟨hfinite, _, disk1, disk2, hdisk1, _, index2, index1, index0,
      _, hedge, hvertex, B, hB⟩ := hCW
    let := hfinite
    have : Finite (_root_.Topology.RelCWComplex.cell (Set.univ : Set (Space pair)) 0) :=
      hfinite.finite_cell 0
    have hvert : ∀ i j, triangle pair i (StdSimplex.single j) ∈
        (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set (Space pair)) 0 :
          Set (Space pair)) := by
      intro i j
      let v : VertexClass pair := ⟨vertex pair (i, j), ⟨(i, j), rfl⟩⟩
      apply _root_.Topology.RelCWComplex.openCell_subset_skeleton 0 (index0 v)
      rw [hvertex]
      exact Set.mem_singleton _
    have heq : ∀ o, edge pair (pair o) = edge pair o := by
      intro o
      ext t
      exact (pairedQuotient_faces_eq face pair o t).symm
    have hzab := cw_pairedTriangles_abelianization_zero α m
      (triangle pair) (edge pair) (fun _ _ _ ↦ rfl) hvert ε d pair hinv hd
      hfree hsign heq hpos (index1 (edgeClass pair d)) disk1 hdisk1
      (hedge d) B hB S (fun t ↦ congrArg (fun e ↦ e t) hS)
    rw [← Abelianization.ker_of]
    exact hzab
  · exact Abelianization.commutator_subset_ker (degreeOneHurewicz x)
end HolomorphicAnosov.Topology
