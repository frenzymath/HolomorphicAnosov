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
/-- A k-subset basis vanishes when k exceeds the number of original coordinates. -/
theorem subset_basis_zero (n k : ℕ)
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (B : Module.Basis {S : Finset (Fin n) // S.card = k} ℚ V) (h : n < k) :
    Subsingleton V := by
  classical
  have : IsEmpty {S : Finset (Fin n) // S.card = k} := ⟨fun S ↦ by
    have hc : S.val.card ≤ n := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ S.val)
    exact (Nat.not_le_of_gt h) (S.property ▸ hc)⟩
  exact B.repr.toEquiv.subsingleton
end HolomorphicAnosov.TorusRationalCupBasisKronecker
