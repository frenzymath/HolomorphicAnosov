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
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SuccessorSubsetIndex

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- The Künneth basis indexed by its two nonzero circle summands becomes the
required coordinate-subset basis, with literal prescribed vectors. Hatcher p.216's
product-basis argument uses this reindexing after identifying its two cup formulas. -/
theorem basis_from_successor_subsets (n k : ℕ)
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : {S : Finset (Fin (n + 1)) // S.card = k + 1} → V)
    (B : Module.Basis ({S : Finset (Fin n) // S.card = k + 1} ⊕
      {S : Finset (Fin n) // S.card = k}) ℚ V)
    (hleft : ∀ S, B (Sum.inl S) = v (successorSubsetIndex n k (Sum.inl S)))
    (hright : ∀ S, B (Sum.inr S) = v (successorSubsetIndex n k (Sum.inr S))) :
    ∃ D : Module.Basis {S : Finset (Fin (n + 1)) // S.card = k + 1} ℚ V,
      ∀ S, D S = v S := by
  refine ⟨B.reindex (successorSubsetIndex n k), ?_⟩
  intro S
  rw [Module.Basis.reindex_apply]
  have he : ∀ t, B t = v (successorSubsetIndex n k t) := by
    intro t
    cases t with
    | inl t => exact hleft t
    | inr t => exact hright t
  rw [he, Equiv.apply_symm_apply]



end HolomorphicAnosov.TorusRationalCupBasisKronecker

