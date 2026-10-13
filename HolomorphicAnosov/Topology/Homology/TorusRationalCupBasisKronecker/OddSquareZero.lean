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
/-- Over the actual rational coefficient field, the degree-one sign law forces every square to
vanish. This uses invertibility of 2, not an invalid implication over a general coefficient ring. -/
theorem odd_square_zero
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (cup : V →ₗ[ℚ] V →ₗ[ℚ] W) (hcomm : ∀ a b, cup a b = -cup b a) (a : V) :
    cup a a = 0 := by
  have hz : (2 : ℚ) • cup a a = 0 := by
    rw [two_smul]
    exact (congrArg (fun x ↦ x + cup a a) (hcomm a a)).trans (neg_add_cancel _)
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
end HolomorphicAnosov.TorusRationalCupBasisKronecker
