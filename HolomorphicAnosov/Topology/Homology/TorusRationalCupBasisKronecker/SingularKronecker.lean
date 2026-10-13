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
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularFieldCohomologyEquiv

import HolomorphicAnosov.AlgebraicTopology.SingularFieldKronecker

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- The actual field Kronecker map for the original singular cochain quotient. Its comparison
with the field-chain provider is fixed by the degreewise functionals, not assumed. -/
def singularKronecker (X : TopCat) (k : ℕ) :
    SingularCochain.cohomology ℚ X k ≃ₗ[ℚ]
      Module.Dual ℚ (((SingularCochain.chainFunctor ℚ).obj X).sc k).moduleCatLeftHomologyData.H := SingularFieldKronecker.singularKronecker (K := ℚ) X k

end HolomorphicAnosov.TorusRationalCupBasisKronecker

