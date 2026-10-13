import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SortEarlierCoordinates
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
/-- Hatcher, Example 3.16, p.216: adjoining the final circle generator puts it
at the end of the increasing monomial, so this step introduces no permutation sign. -/
theorem sort_adjoin_last_coordinate (n : ℕ) (S : Finset (Fin n)) :
    (insert (Fin.last n) (S.map Fin.castSuccEmb)).sort (· ≤ ·) =
      (S.sort (· ≤ ·)).map Fin.castSucc ++ [Fin.last n] := by
  let l := (S.map Fin.castSuccEmb).sort (· ≤ ·)
  have hnot : Fin.last n ∉ l := by
    simp [l]
  have hn : (l ++ [Fin.last n]).Nodup := by
    simp only [List.nodup_append, List.nodup_singleton]
    refine ⟨Finset.sort_nodup _ _, trivial, ?_⟩
    intro i hi j hj
    obtain rfl := List.mem_singleton.mp hj
    intro hij
    exact hnot (hij ▸ hi)
  have hp : (l ++ [Fin.last n]).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨Finset.pairwise_sort _ _, by simp, ?_⟩
    intro i hi j hj
    obtain rfl := List.mem_singleton.mp hj
    exact Fin.le_last i
  have hs := (List.toFinset_sort (r := (· ≤ ·)) hn).mpr hp
  have hf : (l ++ [Fin.last n]).toFinset =
      insert (Fin.last n) (S.map Fin.castSuccEmb) := by
    ext i
    simp [l]
  rw [hf] at hs
  simpa [l, sort_earlier_coordinates] using hs
end HolomorphicAnosov.TorusRationalCupBasisKronecker
