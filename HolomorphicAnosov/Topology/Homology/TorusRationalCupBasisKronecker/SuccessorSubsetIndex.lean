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
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.EarlierCoordinatesMap
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.EarlierCoordinatesRestore
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.EarlierCoordinatesInsertLast
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.LastNotMemEarlier

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- Hatcher, Theorem 3.15 and Example 3.16, p.216: in positive degree the two
surviving circle summands index respectively the subsets omitting and containing the
last coordinate. The inverse restricts to the earlier coordinates. This includes n=0
and degrees above n+1; no nonempty-index assumption is needed. -/
def successorSubsetIndex (n k : ℕ) :
    ({S : Finset (Fin n) // S.card = k + 1} ⊕
      {S : Finset (Fin n) // S.card = k}) ≃
      {S : Finset (Fin (n + 1)) // S.card = k + 1} := by
  let f : ({S : Finset (Fin n) // S.card = k + 1} ⊕
      {S : Finset (Fin n) // S.card = k}) →
      {S : Finset (Fin (n + 1)) // S.card = k + 1} :=
    Sum.elim
      (fun S ↦ ⟨S.val.map Fin.castSuccEmb, by simpa using S.property⟩)
      (fun S ↦ ⟨insert (Fin.last n) (S.val.map Fin.castSuccEmb), by
        rw [Finset.card_insert_of_notMem (last_not_mem_earlier n S.val), Finset.card_map]
        rw [S.property]⟩)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro s t h
    have hv := congrArg Subtype.val h
    cases s with
    | inl s =>
      cases t with
      | inl t =>
        have he := congrArg (earlierCoordinates n) hv
        simp only [f, Sum.elim_inl, earlierCoordinates_restore] at he
        exact congrArg Sum.inl (Subtype.ext he)
      | inr t =>
        have hm : Fin.last n ∈ s.val.map Fin.castSuccEmb := by
          rw [show s.val.map Fin.castSuccEmb =
            insert (Fin.last n) (t.val.map Fin.castSuccEmb) from hv]
          exact Finset.mem_insert_self _ _
        exact False.elim (last_not_mem_earlier n s.val hm)
    | inr s =>
      cases t with
      | inl t =>
        have hm : Fin.last n ∈ t.val.map Fin.castSuccEmb := by
          rw [show t.val.map Fin.castSuccEmb =
            insert (Fin.last n) (s.val.map Fin.castSuccEmb) from hv.symm]
          exact Finset.mem_insert_self _ _
        exact False.elim (last_not_mem_earlier n t.val hm)
      | inr t =>
        have he := congrArg (earlierCoordinates n) hv
        simp only [f, Sum.elim_inr, earlierCoordinates_insert_last] at he
        exact congrArg Sum.inr (Subtype.ext he)
  · intro S
    have hc := congrArg Finset.card (earlierCoordinates_map n S.val)
    rw [Finset.card_map] at hc
    by_cases hlast : Fin.last n ∈ S.val
    · have hk : (earlierCoordinates n S.val).card = k := by
        rw [Finset.card_erase_of_mem hlast, S.property] at hc
        omega
      refine ⟨Sum.inr ⟨earlierCoordinates n S.val, hk⟩, ?_⟩
      apply Subtype.ext
      change insert (Fin.last n) ((earlierCoordinates n S.val).map Fin.castSuccEmb) = S.val
      rw [earlierCoordinates_map, Finset.insert_erase hlast]
    · have hk : (earlierCoordinates n S.val).card = k + 1 := by
        rw [Finset.erase_eq_of_notMem hlast, S.property] at hc
        exact hc
      refine ⟨Sum.inl ⟨earlierCoordinates n S.val, hk⟩, ?_⟩
      apply Subtype.ext
      change (earlierCoordinates n S.val).map Fin.castSuccEmb = S.val
      rw [earlierCoordinates_map, Finset.erase_eq_of_notMem hlast]


end HolomorphicAnosov.TorusRationalCupBasisKronecker

