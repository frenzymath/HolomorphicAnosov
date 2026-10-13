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
/-- Pullback preserves the literal constant-one cochain, before passage to the
cohomology quotient. Hatcher pp.201 and 207; postcomposition takes each singular
zero-simplex generator to one singular zero-simplex generator. -/
theorem pullback_oneCochain {X Y : TopCat} (f : X ⟶ Y) :
    (SingularCochain.pullback ℚ f).f 0 (SingularCochain.oneCochain ℚ Y) =
      SingularCochain.oneCochain ℚ X := by
  change (((SingularCochain.chainFunctor ℚ).map f).f 0) ≫
    SingularCochain.oneCochain ℚ Y = SingularCochain.oneCochain ℚ X
  apply SSet.chainComplex_hom_ext
  intro σ
  dsimp only [SingularCochain.oneCochain]
  rw [← Category.assoc]
  change ((TopCat.toSSet.obj X).ιChainComplex σ ≫
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f 0) ≫ _ = _
  rw [SSet.ι_chainComplexMap_f]
  simp [SSet.ιChainComplex]
end HolomorphicAnosov.TorusRationalCupBasisKronecker
