import HolomorphicAnosov.Topology.LoopSingularClass
import HolomorphicAnosov.Topology.ModuleCatCycleClassEqOfBoundary
import HolomorphicAnosov.Topology.SimplicialTwoTriangleBoundary
import HolomorphicAnosov.Topology.PathHomotopySingularTriangles

noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- Endpoint-fixed homotopies of loops preserve their native singular classes.

Source and proof: Hatcher, Theorem 2A.1, p.166. Triangulate the homotopy
square by its diagonal. The two singular triangles have equal diagonal
faces. Their side faces are both the constant basepoint since the loops
have the same basepoint. Thus their difference has boundary exactly the
initial loop minus the final loop. The native module homology quotient
identifies these two cycle classes. -/
theorem loopSingularClass_homotopic {X : Type u} [TopologicalSpace X]
    {x : X} {α β : Path x x} (h : α.Homotopic β) :
    loopSingularClass α = loopSingularClass β := by
  obtain ⟨H⟩ := h
  obtain ⟨s, t, hside, hdiag, hs, ht⟩ := pathHomotopy_singular_triangles H
  let Y := TopCat.toSSet.obj (TopCat.of X)
  let R := ModuleCat.of ℤ (ULift.{u} ℤ)
  let c := (Y.ιChainComplex (R := R) s) (1 : R) -
    (Y.ιChainComplex (R := R) t) (1 : R)
  have hb := simplicial_two_triangle_boundary Y R s t hside hdiag (1 : R)
  rw [hs, ht] at hb
  have hex : ∃ c' : ((integralSingularChains X).sc 1).X₁,
      ((integralSingularChains X).sc 1).f c' = pathSingularChain α - pathSingularChain β := by
    dsimp +instances only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor']
    rw [ComplexShape.prev_eq' (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel 2 1 from rfl)]
    exact ⟨c, hb⟩
  obtain ⟨c', hc'⟩ := hex
  exact moduleCat_cycleClass_eq_of_boundary ((integralSingularChains X).sc 1)
    ⟨pathSingularChain α, loopSingularChain_isCycle α⟩
    ⟨pathSingularChain β, loopSingularChain_isCycle β⟩ c' hc'

end HolomorphicAnosov.Topology
