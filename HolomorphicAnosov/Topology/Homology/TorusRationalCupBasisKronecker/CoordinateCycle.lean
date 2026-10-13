import HolomorphicAnosov.Algebra.Homology.FieldChainKroneckerEvaluation
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CoordinateInclusion

open CategoryTheory
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- Push the original circle cycle by the actual native singular chain map. -/
def coordinateCycle (n : ℕ)
    (z : LinearMap.ker (((SingularCochain.chainFunctor ℚ).obj
      (TopCat.of UnitAddCircle)).sc 1).g.hom) (i : Fin n) :
    LinearMap.ker (((SingularCochain.chainFunctor ℚ).obj
      (TopCat.of (UnitAddTorus (Fin n)))).sc 1).g.hom :=
  ⟨(((SingularCochain.chainFunctor ℚ).map (coordinateInclusion n i)).f 1) z.val,
    FieldChainKronecker.map_cycle_mem
      ((SingularCochain.chainFunctor ℚ).map (coordinateInclusion n i)) 1 z⟩

end HolomorphicAnosov.TorusRationalCupBasisKronecker
