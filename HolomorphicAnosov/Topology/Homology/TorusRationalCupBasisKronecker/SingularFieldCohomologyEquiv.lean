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
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularDualIso

import HolomorphicAnosov.AlgebraicTopology.SingularFieldKronecker

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

set_option backward.isDefEq.respectTransparency false in
/-- Canonical transport between the two literal kernel/image quotient presentations of singular
cohomology, induced by the degreewise functional identification. -/
def singularFieldCohomologyEquiv (X : TopCat) (k : ℕ) :
    SingularCochain.cohomology ℚ X k ≃ₗ[ℚ]
      FieldChainKronecker.cohomology ((SingularCochain.chainFunctor ℚ).obj X) k := SingularFieldKronecker.singularFieldCohomologyEquiv (K := ℚ) X k

end HolomorphicAnosov.TorusRationalCupBasisKronecker

