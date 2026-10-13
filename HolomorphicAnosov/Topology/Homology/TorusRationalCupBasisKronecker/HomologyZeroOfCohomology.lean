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
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularKronecker

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- Above a zero cohomology degree the full-dual Kronecker equivalence forces zero homology,
without an independent dimension or nonempty-space assumption. -/
theorem homology_zero_of_cohomology (X : TopCat) (k : ℕ)
    [Subsingleton (SingularCochain.cohomology ℚ X k)] :
    Subsingleton (((SingularCochain.chainFunctor ℚ).obj X).sc k).moduleCatLeftHomologyData.H := by
  have := (singularKronecker X k).toEquiv.symm.subsingleton
  exact (Module.subsingleton_dual_iff ℚ).mp inferInstance


end HolomorphicAnosov.TorusRationalCupBasisKronecker

