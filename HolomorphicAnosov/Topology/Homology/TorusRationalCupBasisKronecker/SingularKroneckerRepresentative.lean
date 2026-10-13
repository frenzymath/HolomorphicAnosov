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
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.QuotientMapRepresentative

import HolomorphicAnosov.AlgebraicTopology.SingularFieldKronecker

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

set_option backward.isDefEq.respectTransparency false in
/-- The singular Kronecker equivalence evaluates every original cocycle/cycle pair literally. -/
theorem singularKronecker_representative (X : TopCat) (k : ℕ)
    (a : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) k)
    (z : LinearMap.ker (((SingularCochain.chainFunctor ℚ).obj X).sc k).g.hom) :
    singularKronecker X k
        (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) k a)
        ((((SingularCochain.chainFunctor ℚ).obj X).sc k).moduleCatLeftHomologyData.π z) =
      (show ((SingularCochain.chainFunctor ℚ).obj X).X k ⟶ ModuleCat.of ℚ ℚ from a.val)
        z.val := SingularFieldKronecker.singularKronecker_representative X k a z

end HolomorphicAnosov.TorusRationalCupBasisKronecker

