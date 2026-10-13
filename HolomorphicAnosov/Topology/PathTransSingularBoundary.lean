import HolomorphicAnosov.Topology.PathTransSingularTriangle
import HolomorphicAnosov.Topology.PathSingularChain

noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- The sum of two composable path chains minus their concatenation is a boundary.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.166. The concatenation
triangle has ordered faces second path, concatenation, first path. Apply the
native alternating face differential and reorder its three terms. -/
theorem pathTrans_singular_boundary {X : Type u} [TopologicalSpace X]
    {x y z : X} (α : Path x y) (β : Path y z) :
    ∃ c : (integralSingularChains X).X 2,
      ((integralSingularChains X).d 2 1) c =
        pathSingularChain α + pathSingularChain β - pathSingularChain (α.trans β) := by
  obtain ⟨s, h0, h1, h2⟩ := pathTrans_singular_triangle α β
  let Y := TopCat.toSSet.obj (TopCat.of X)
  let R := ModuleCat.of ℤ (ULift.{u} ℤ)
  refine ⟨(Y.ιChainComplex (R := R) s) (1 : R), ?_⟩
  have hb := congrArg (fun f ↦ f.hom (1 : R)) (Y.ιChainComplex_d (R := R) s)
  change ((Y.chainComplex R).d 2 1).hom ((Y.ιChainComplex (R := R) s).hom 1) = _ at hb
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hb
  change ((Y.chainComplex R).d 2 1).hom ((Y.ιChainComplex (R := R) s).hom 1) = _
  rw [hb]
  simp [Y, h0, h1, h2, pathSingularChain, R]
  abel

end HolomorphicAnosov.Topology
