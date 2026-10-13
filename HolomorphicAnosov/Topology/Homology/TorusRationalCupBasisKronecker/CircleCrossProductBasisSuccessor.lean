import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SuccessorCircleTensorIndex
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleCrossProductBasis

open CategoryTheory
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- Hatcher Theorem 3.15 and Example 3.16, p.216: the native product basis
reindexed into the two successor subset branches has the literal cup values
with the circle degree-zero and degree-one basis vectors. Both degree sums
reduce definitionally, so no extra cast or abstract rank premise remains. -/
theorem circle_cross_product_basis_successor (n : ℕ) (X Y : TopCat)
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)]
    [Topology.CWComplex.Finite (Set.univ : Set X)]
    [Topology.CWComplex (Set.univ : Set Y)]
    [Topology.CWComplex.Finite (Set.univ : Set Y)]
    (BX : ∀ p, Module.Basis {S : Finset (Fin n) // S.card = p} ℚ
      (SingularCochain.cohomology ℚ X p))
    (B₀ : Module.Basis Unit ℚ (SingularCochain.cohomology ℚ Y 0))
    (B₁ : Module.Basis Unit ℚ (SingularCochain.cohomology ℚ Y 1))
    (hz : ∀ q, 2 ≤ q → Subsingleton (SingularCochain.cohomology ℚ Y q))
    (cup : ∀ p q : ℕ, SingularCochain.cohomology ℚ (SingularCochain.crossProductSpace X Y) p →ₗ[ℚ]
      SingularCochain.cohomology ℚ (SingularCochain.crossProductSpace X Y) q →ₗ[ℚ] SingularCochain.cohomology ℚ (SingularCochain.crossProductSpace X Y) (p + q))
    (hcup : ∀ p q (b : SingularCochain.cycles ℚ (SingularCochain.complex ℚ (SingularCochain.crossProductSpace X Y)) p)
        (c : SingularCochain.cycles ℚ (SingularCochain.complex ℚ (SingularCochain.crossProductSpace X Y)) q),
      ∃ hc : SingularCochain.cupCochain ℚ (SingularCochain.crossProductSpace X Y) b.val c.val ∈
          SingularCochain.cycles ℚ (SingularCochain.complex ℚ (SingularCochain.crossProductSpace X Y)) (p + q),
        cup p q (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ (SingularCochain.crossProductSpace X Y)) p b)
          (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ (SingularCochain.crossProductSpace X Y)) q c) =
          SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ (SingularCochain.crossProductSpace X Y)) (p + q)
            ⟨SingularCochain.cupCochain ℚ (SingularCochain.crossProductSpace X Y) b.val c.val, hc⟩)
    (k : ℕ) :
    ∃ B : Module.Basis ({S : Finset (Fin n) // S.card = k + 1} ⊕
        {S : Finset (Fin n) // S.card = k}) ℚ
        (SingularCochain.cohomology ℚ (SingularCochain.crossProductSpace X Y) (k + 1)),
      (∀ S, B (Sum.inl S) = cup (k + 1) 0
        ((SingularCochain.cohomologyPullback ℚ
          (SingularCochain.crossProductFst X Y) (k + 1)).hom (BX (k + 1) S))
        ((SingularCochain.cohomologyPullback ℚ
          (SingularCochain.crossProductSnd X Y) 0).hom (B₀ ()))) ∧
      (∀ S, B (Sum.inr S) = cup k 1
        ((SingularCochain.cohomologyPullback ℚ
          (SingularCochain.crossProductFst X Y) k).hom (BX k S))
        ((SingularCochain.cohomologyPullback ℚ
          (SingularCochain.crossProductSnd X Y) 1).hom (B₁ ()))) := by
  obtain ⟨B, hB⟩ := circle_cross_product_basis n X Y BX B₀ B₁ hz cup hcup (k + 1)
  refine ⟨B.reindex (successorCircleTensorIndex n k).symm, ?_, ?_⟩
  · intro S
    have he : successorCircleTensorIndex n k (Sum.inl S) =
        ⟨⟨(k + 1, 0), by omega⟩, S, ()⟩ := rfl
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, he]
    have hv := hB ⟨(k + 1, 0), by omega⟩ S ()
    convert hv using 1; rfl
  · intro S
    have he : successorCircleTensorIndex n k (Sum.inr S) =
        ⟨⟨(k, 1), rfl⟩, S, ()⟩ := rfl
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, he]
    have hv := hB ⟨(k, 1), rfl⟩ S ()
    convert hv using 1; rfl

end HolomorphicAnosov.TorusRationalCupBasisKronecker
