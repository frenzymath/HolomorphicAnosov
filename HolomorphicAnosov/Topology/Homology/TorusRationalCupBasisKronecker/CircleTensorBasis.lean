import HolomorphicAnosov.AlgebraicTopology.FiniteCWCohomologyCrossProductKunneth
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.DFinsupp
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleProfileBasis
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleTensorIndex

open CategoryTheory
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- Construct the native Künneth tensor-direct-sum basis from the induction basis
and the source circle profile. Every vector is the original pure tensor in its
original summand; vanishing higher circle degrees contribute empty index sets.
Source: Hatcher, Theorem 3.15 and Example 3.16, p.216. -/
def circleTensorBasis (n k : ℕ) (X Y : TopCat)
    (BX : ∀ p, Module.Basis {S : Finset (Fin n) // S.card = p} ℚ
      (SingularCochain.cohomology ℚ X p))
    (B₀ : Module.Basis Unit ℚ (SingularCochain.cohomology ℚ Y 0))
    (B₁ : Module.Basis Unit ℚ (SingularCochain.cohomology ℚ Y 1))
    (hz : ∀ q, 2 ≤ q → Subsingleton (SingularCochain.cohomology ℚ Y q)) :
    Module.Basis (circleTensorIndex n k) ℚ
      (SingularCochain.crossProductDegreeDomain ℚ X Y k) :=
  DFinsupp.basis fun i =>
    (BX i.val.1).tensorProduct (circleProfileBasis B₀ B₁ hz i.val.2)

end HolomorphicAnosov.TorusRationalCupBasisKronecker
