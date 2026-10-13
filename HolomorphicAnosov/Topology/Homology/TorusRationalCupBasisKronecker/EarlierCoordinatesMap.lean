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
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.EarlierCoordinates

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- Removing the final coordinate and then restoring the earlier labels gives its erasure. -/
theorem earlierCoordinates_map (n : ℕ) (S : Finset (Fin (n + 1))) :
    (earlierCoordinates n S).map Fin.castSuccEmb = S.erase (Fin.last n) := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp
  · simp [earlierCoordinates]


end HolomorphicAnosov.TorusRationalCupBasisKronecker

