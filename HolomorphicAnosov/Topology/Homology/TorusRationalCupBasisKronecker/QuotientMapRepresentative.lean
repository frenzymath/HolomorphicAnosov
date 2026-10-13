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

import HolomorphicAnosov.AlgebraicTopology.SingularFieldKronecker

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker
set_option backward.isDefEq.respectTransparency false in
/-- The module-homology comparison sends a literal cocycle class to the class of its actual
component image. This is homology projection naturality, evaluated at the original cocycle. -/
theorem quotient_map_representative
    {ι : Type*} {c : ComplexShape ι}
    {Q Q' : HomologicalComplex (ModuleCat ℚ) c} (F : Q ⟶ Q') (k : ι)
    (a : LinearMap.ker (Q.sc k).g.hom) (b : LinearMap.ker (Q'.sc k).g.hom)
    (hab : (F.f k) a.val = b.val) :
    ((Q.sc k).moduleCatHomologyIso.inv ≫ HomologicalComplex.homologyMap F k ≫
      (Q'.sc k).moduleCatHomologyIso.hom) ((Q.sc k).moduleCatLeftHomologyData.π a) =
        (Q'.sc k).moduleCatLeftHomologyData.π b := SingularFieldKronecker.quotient_map_representative F k a b hab

end HolomorphicAnosov.TorusRationalCupBasisKronecker
