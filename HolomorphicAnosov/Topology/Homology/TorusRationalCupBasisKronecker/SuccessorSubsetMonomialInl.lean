import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SuccessorSubsetIndex
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SortEarlierCoordinates

open CategoryTheory
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- Hatcher, Algebraic Topology, Example 3.16 p216 does not give the native successor-subset and dependent-degree cast formula. The agent-written proof uses the existing sorted-list mapping theorem and equality elimination to identify the two cast monomials. This is a direct implementation specialization, not a proof printed in Hatcher.

DAG node: `topo.torus_public_successor_subset_monomial_inl_g17`. -/
theorem successor_subset_monomial_inl
    (n : ℕ) (X : TopCat)
    (cup : ∀ p q : ℕ, SingularCochain.cohomology ℚ X p →ₗ[ℚ]
      SingularCochain.cohomology ℚ X q →ₗ[ℚ]
        SingularCochain.cohomology ℚ X (p + q))
    (one : SingularCochain.cohomology ℚ X 0)
    (alpha : Fin (n + 1) → SingularCochain.cohomology ℚ X 1)
    (k : ℕ) (S : {S : Finset (Fin n) // S.card = k + 1}) :
    let H := fun d ↦ (SingularCochain.cohomology ℚ X d : Type)
    let m : ∀ l : List (Fin (n + 1)), H l.length :=
      fun l ↦ List.rec (motive := fun l ↦ H l.length) one
        (fun i l v ↦ cast (congrArg H (Nat.add_comm 1 l.length))
          (cup 1 l.length (alpha i) v)) l
    let T := successorSubsetIndex n k (Sum.inl S)
    cast (congrArg H ((T.val.length_sort (· ≤ ·)).trans T.property))
      (m (T.val.sort (· ≤ ·))) =
      cast (congrArg H
        ((by simp : ((S.val.sort (· ≤ ·)).map Fin.castSucc).length =
          (S.val.sort (· ≤ ·)).length).trans
          ((S.val.length_sort (· ≤ ·)).trans S.property)))
        (m ((S.val.sort (· ≤ ·)).map Fin.castSucc)) := by
  dsimp
  apply eq_of_heq
  refine HEq.trans (cast_heq _ _) ?_
  have hT : (successorSubsetIndex n k (Sum.inl S)).val =
      S.val.map Fin.castSuccEmb := rfl
  have hl : (successorSubsetIndex n k (Sum.inl S)).val.sort (· ≤ ·) =
      (S.val.sort (· ≤ ·)).map Fin.castSucc := by
    rw [hT]
    exact sort_earlier_coordinates n S.val
  rw [hl]
  exact (cast_heq _ _).symm

end HolomorphicAnosov.TorusRationalCupBasisKronecker
