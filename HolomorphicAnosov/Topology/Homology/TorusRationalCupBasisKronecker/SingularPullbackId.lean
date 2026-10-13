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

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker
set_option backward.isDefEq.respectTransparency false in
/-- Identity pullback acts as identity on the literal singular cohomology quotient. -/
theorem singularPullback_id (X : TopCat) (k : ℕ) :
    SingularCochain.cohomologyPullback ℚ (𝟙 X) k = 𝟙 _ := by
  unfold SingularCochain.cohomologyPullback SingularCochain.quotientMap
  have he : SingularCochain.pullback ℚ (𝟙 X) = 𝟙 _ :=
    (SingularCochain.cochainFunctor ℚ).map_id _
  rw [he, HomologicalComplex.homologyMap_id]
  exact (Category.comp_id _).trans
    ((SingularCochain.complex ℚ X).sc k).moduleCatHomologyIso.inv_hom_id
end HolomorphicAnosov.TorusRationalCupBasisKronecker
