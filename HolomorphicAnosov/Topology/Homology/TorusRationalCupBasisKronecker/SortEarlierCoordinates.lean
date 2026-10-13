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
/-- Hatcher, Theorem 3.15 and Example 3.16, p.216: the first Künneth summand
retains a subset of the earlier coordinates. Its increasing order is preserved. -/
theorem sort_earlier_coordinates (n : ℕ) (S : Finset (Fin n)) :
    (S.map Fin.castSuccEmb).sort (· ≤ ·) = (S.sort (· ≤ ·)).map Fin.castSucc := by
  symm
  exact Finset.map_sort Fin.castSuccEmb S (· ≤ ·) (· ≤ ·) (by intros; rfl)
end HolomorphicAnosov.TorusRationalCupBasisKronecker
