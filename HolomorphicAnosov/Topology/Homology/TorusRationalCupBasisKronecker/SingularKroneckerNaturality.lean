import HolomorphicAnosov.Algebra.Homology.FieldChainKroneckerEvaluation
import HolomorphicAnosov.AlgebraicTopology.FiniteCWCohomologyCrossProductKunneth
import HolomorphicAnosov.AlgebraicTopology.SingularCupProductLaws
import HolomorphicAnosov.Topology.CircleSingularCohomologyWinding
import HolomorphicAnosov.Topology.RealTorusCoordinateCWStructure
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductDefinition
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Finset.Sort
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularKroneckerRepresentative
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.QuotientMapRepresentative

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the actual singular pairing on every class follows by choosing original
representatives and evaluating the same chain map on either side. -/
theorem singularKronecker_naturality {X Y : TopCat} (f : X ⟶ Y) (k : ℕ)
    (a : SingularCochain.cohomology ℚ Y k)
    (z : (((SingularCochain.chainFunctor ℚ).obj X).sc k).moduleCatLeftHomologyData.H) :
    singularKronecker X k ((SingularCochain.cohomologyPullback ℚ f k) a) z =
      singularKronecker Y k a
        (((((SingularCochain.chainFunctor ℚ).obj X).sc k).moduleCatHomologyIso.inv ≫
          HomologicalComplex.homologyMap ((SingularCochain.chainFunctor ℚ).map f) k ≫
          (((SingularCochain.chainFunctor ℚ).obj Y).sc k).moduleCatHomologyIso.hom) z) := by
  have ha : Function.Surjective
      (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ Y) k) :=
    Submodule.mkQ_surjective _
  have hz : Function.Surjective
      ((((SingularCochain.chainFunctor ℚ).obj X).sc k).moduleCatLeftHomologyData.π) :=
    Submodule.mkQ_surjective _
  obtain ⟨a, rfl⟩ := ha a
  obtain ⟨z, rfl⟩ := hz z
  let a' : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) k :=
    ⟨(SingularCochain.pullback ℚ f).f k a.val,
      FieldChainKronecker.map_cycle_mem (SingularCochain.pullback ℚ f) k a⟩
  let z' : LinearMap.ker (((SingularCochain.chainFunctor ℚ).obj Y).sc k).g.hom :=
    ⟨(((SingularCochain.chainFunctor ℚ).map f).f k) z.val,
      FieldChainKronecker.map_cycle_mem ((SingularCochain.chainFunctor ℚ).map f) k z⟩
  have hap : (SingularCochain.cohomologyPullback ℚ f k)
      (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ Y) k a) =
      SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) k a' :=
    quotient_map_representative _ k a a' rfl
  have hzp := quotient_map_representative ((SingularCochain.chainFunctor ℚ).map f) k z z' rfl
  change singularKronecker X k _ _ = singularKronecker Y k _ _
  rw [hap, hzp, singularKronecker_representative, singularKronecker_representative]
  rfl


end HolomorphicAnosov.TorusRationalCupBasisKronecker

