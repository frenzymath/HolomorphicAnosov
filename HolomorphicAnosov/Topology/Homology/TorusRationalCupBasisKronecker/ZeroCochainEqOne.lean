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
/-- A zero-cochain with value one on every original singular simplex is the
literal constant-one cochain. Hatcher pp.197 and 207. The free-chain coproduct
extensionality and linearity reduce equality to coefficient-one generators. -/
theorem zeroCochain_eq_one (X : TopCat)
    (a : SingularCochain.cochains ℚ X 0)
    (ha : ∀ σ : (TopCat.toSSet.obj X) _⦋0⦌,
      a.hom (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom 1) = 1) :
    a = SingularCochain.oneCochain ℚ X := by
  apply SSet.chainComplex_hom_ext
  intro σ
  have hi : (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ ≫ a =
      𝟙 (ModuleCat.of ℚ ℚ) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change a.hom (((TopCat.toSSet.obj X).ιChainComplex
      (R := ModuleCat.of ℚ ℚ) σ).hom 1) = 1
    exact ha σ
  simpa [SingularCochain.oneCochain, SSet.ιChainComplex] using hi
end HolomorphicAnosov.TorusRationalCupBasisKronecker
