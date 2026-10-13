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
/-- Mapping a one-simplex obtained from a loop through the singular-set functor is literal
postcomposition of that loop. -/
theorem singularOneSimplex_naturality {X Y : TopCat} (f : X ⟶ Y) (γ : TopCat.I ⟶ X) :
    (TopCat.toSSet.map f).app (op ⦋1⦌) (TopCat.toSSetObj₁Equiv.symm γ) =
      TopCat.toSSetObj₁Equiv.symm (γ ≫ f) := by
  apply TopCat.toSSetObj₁Equiv.injective
  ext t
  rfl
end HolomorphicAnosov.TorusRationalCupBasisKronecker
