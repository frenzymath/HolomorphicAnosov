import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.DirectSumBasisApply
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleBasisIndex
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleProfileBasis
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleTensorBasis

open CategoryTheory
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- Explicit pure tensors for the constructed Künneth basis, in all degrees.
Hatcher p.216; follows from the tensor and dependent-direct-sum basis formulas. -/
theorem circleTensorBasis_apply (n k : ℕ) (X Y : TopCat)
    (BX : ∀ p, Module.Basis {S : Finset (Fin n) // S.card = p} ℚ
      (SingularCochain.cohomology ℚ X p))
    (B₀ : Module.Basis Unit ℚ (SingularCochain.cohomology ℚ Y 0))
    (B₁ : Module.Basis Unit ℚ (SingularCochain.cohomology ℚ Y 1))
    (hz : ∀ q, 2 ≤ q → Subsingleton (SingularCochain.cohomology ℚ Y q))
    (i : {i : ℕ × ℕ // i.1 + i.2 = k})
    (S : {S : Finset (Fin n) // S.card = i.val.1}) (j : circleBasisIndex i.val.2) :
    circleTensorBasis n k X Y BX B₀ B₁ hz ⟨i, S, j⟩ =
      DirectSum.lof ℚ _ _ i
        (TensorProduct.tmul ℚ (BX i.val.1 S) (circleProfileBasis B₀ B₁ hz i.val.2 j)) := by
  rw [circleTensorBasis, directSum_basis_apply, Module.Basis.tensorProduct_apply]

end HolomorphicAnosov.TorusRationalCupBasisKronecker
