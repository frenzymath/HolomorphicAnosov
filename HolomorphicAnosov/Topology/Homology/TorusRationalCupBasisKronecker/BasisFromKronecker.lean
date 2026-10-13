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
/-- A finite cohomology basis and its exact Kronecker matrix identify a specified family of
homology vectors as the dual basis. This is only an algebraic consequence used after the genuine
coordinate cup basis is constructed; it does not add a hypothesis to the public theorem. -/
theorem basis_from_kronecker
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Module.Basis ι ℚ W) (E : W ≃ₗ[ℚ] Module.Dual ℚ V)
    (w : ι → V) (hw : ∀ i j, E (B i) (w j) = if i = j then 1 else 0) :
    ∃ D : Module.Basis ι ℚ V, ∀ j, D j = w j := by
  let B' := B.map E
  have : FiniteDimensional ℚ (Module.Dual ℚ V) := Module.Finite.of_basis B'
  have : FiniteDimensional ℚ V := (Module.finite_dual_iff ℚ).mp inferInstance
  let D := B'.dualBasis.map (Module.evalEquiv ℚ V).symm
  refine ⟨D, ?_⟩
  intro j
  apply (Module.evalEquiv ℚ V).injective
  apply B'.ext
  intro i
  change E (B i) (D j) = E (B i) (w j)
  rw [hw]
  change (Module.evalEquiv ℚ V) (D j) (B' i) = _
  simp [D, Finsupp.single_apply, eq_comm]
end HolomorphicAnosov.TorusRationalCupBasisKronecker
