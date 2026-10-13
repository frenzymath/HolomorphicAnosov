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
/-- The native singular quotient pullback is functorial, since it conjugates the native
homology functor by its module-kernel/image identification. -/
theorem singularPullback_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) (k : ℕ) :
    SingularCochain.cohomologyPullback ℚ (f ≫ g) k =
      SingularCochain.cohomologyPullback ℚ g k ≫
        SingularCochain.cohomologyPullback ℚ f k := by
  unfold SingularCochain.cohomologyPullback SingularCochain.quotientMap
  have he : SingularCochain.pullback ℚ (f ≫ g) =
      SingularCochain.pullback ℚ g ≫ SingularCochain.pullback ℚ f := by
    exact (SingularCochain.cochainFunctor ℚ).map_comp g.op f.op
  rw [he, HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
end HolomorphicAnosov.TorusRationalCupBasisKronecker
