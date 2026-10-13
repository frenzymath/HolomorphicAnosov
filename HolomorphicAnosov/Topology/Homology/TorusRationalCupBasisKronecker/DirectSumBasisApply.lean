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
/-- The explicit vectors of Mathlib's dependent-direct-sum basis are the original
summand injections. This is the algebraic basis construction in Hatcher p.216,
with no classification or Künneth hypothesis. -/
theorem directSum_basis_apply {ι : Type} {η : ι → Type} {M : ι → Type}
    [DecidableEq ι]
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℚ (M i)]
    (B : ∀ i, Module.Basis (η i) ℚ (M i)) (i : ι) (j : η i) :
    DFinsupp.basis B ⟨i, j⟩ = DirectSum.lof ℚ ι M i (B i j) := by
  classical
  apply Module.Basis.apply_eq_iff.mpr
  ext ⟨i', j'⟩
  change (B i').repr ((DirectSum.lof ℚ ι M i) (B i j) i') j' =
    Finsupp.single (⟨i, j⟩ : Σ i, η i) (1 : ℚ) ⟨i', j'⟩
  by_cases h : i = i'
  · subst i'
    simp [Finsupp.single_apply_left sigma_mk_injective]
  · simp [DirectSum.lof_eq_of, DirectSum.of_apply, h]
end HolomorphicAnosov.TorusRationalCupBasisKronecker
