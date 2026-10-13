import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.KunnethWithSpecifiedCup
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleBasisIndex
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleProfileBasis
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleTensorIndex
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleTensorBasis
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleTensorBasisApply

open CategoryTheory
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- The native product basis, constructed from the induction bases and the
circle profile, has exactly the original cup cross-product vectors in every
degree. Hatcher, Theorem 3.15 and Example 3.16, p.216. The finite-free hypothesis
on the circle is proved from its actual singleton/empty bases; no Künneth
isomorphism or product basis is assumed. The casts are only the original
p+q=k degree identifications. -/
theorem circle_cross_product_basis (n : ℕ) (X Y : TopCat)
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
    ∃ B : Module.Basis (circleTensorIndex n k) ℚ
        (SingularCochain.cohomology ℚ (SingularCochain.crossProductSpace X Y) k),
      ∀ (i : {i : ℕ × ℕ // i.1 + i.2 = k})
        (S : {S : Finset (Fin n) // S.card = i.val.1})
        (j : circleBasisIndex i.val.2),
        B ⟨i, S, j⟩ = cast (congrArg
          (fun d ↦ (SingularCochain.cohomology ℚ
            (SingularCochain.crossProductSpace X Y) d : Type)) i.property)
          (cup i.val.1 i.val.2
            ((SingularCochain.cohomologyPullback ℚ
              (SingularCochain.crossProductFst X Y) i.val.1).hom (BX i.val.1 S))
            ((SingularCochain.cohomologyPullback ℚ
              (SingularCochain.crossProductSnd X Y) i.val.2).hom
              (circleProfileBasis B₀ B₁ hz i.val.2 j))) := by
  have hfree : ∀ q, Module.Free ℚ (SingularCochain.cohomology ℚ Y q) ∧
      Module.Finite ℚ (SingularCochain.cohomology ℚ Y q) := by
    intro q
    have : Finite (circleBasisIndex q) := by
      dsimp only [circleBasisIndex]
      split <;> infer_instance
    exact ⟨Module.Free.of_basis (circleProfileBasis B₀ B₁ hz q),
      Module.Finite.of_basis (circleProfileBasis B₀ B₁ hz q)⟩
  obtain ⟨μ, hμ⟩ := kunneth_with_specified_cup X Y hfree cup hcup k
  refine ⟨(circleTensorBasis n k X Y BX B₀ B₁ hz).map μ, ?_⟩
  intro i S j
  rw [Module.Basis.map_apply, circleTensorBasis_apply]
  exact hμ i (BX i.val.1 S) (circleProfileBasis B₀ B₁ hz i.val.2 j)

end HolomorphicAnosov.TorusRationalCupBasisKronecker
