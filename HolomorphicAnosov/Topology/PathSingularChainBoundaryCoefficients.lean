import HolomorphicAnosov.Topology.SingularChainGeneratorIso
import HolomorphicAnosov.Topology.SingularChainBoundary
import HolomorphicAnosov.Topology.PathSingularChain

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- The finite coefficients of a path boundary are its target minus its source.
Source: Hatcher, Algebraic Topology, p.166. Expand the native degree-one
alternating boundary, use the actual path endpoint faces, and apply the
canonical singular-chain coefficient comparison to each zero-simplex. -/
theorem pathSingularChain_boundary_coefficients {X : Type u} [TopologicalSpace X]
    {x y : X} (α : Path x y) :
    (singularChainGeneratorIso (TopCat.of X) 0).hom
      (((integralSingularChains X).d 1 0) (pathSingularChain α)) =
      Finsupp.single (ContinuousMap.const _ y) (1 : ULift.{u} ℤ) -
        Finsupp.single (ContinuousMap.const _ x) 1 := by
  have h := singularChainGeneratorIso_hom_boundary (TopCat.of X) 0
    (pathSingularSimplex α) (1 : ULift.{u} ℤ)
  have h0 : ((TopCat.pathEquiv (X := TopCat.of X)).symm α).hom 0 = x := ((TopCat.pathEquiv (X := TopCat.of X)).symm α).hom₀
  have h1 : ((TopCat.pathEquiv (X := TopCat.of X)).symm α).hom 1 = y := ((TopCat.pathEquiv (X := TopCat.of X)).symm α).hom₁
  simpa [Fin.sum_univ_two, pathSingularChain, pathSingularSimplex,
    TopCat.toSSetObj₀Equiv, h0, h1, sub_eq_add_neg, integralSingularChains,
    ContinuousMap.const] using h
end HolomorphicAnosov.Topology
