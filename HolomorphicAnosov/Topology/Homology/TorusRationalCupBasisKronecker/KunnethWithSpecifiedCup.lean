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
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.GradedMulEqSpecifiedCup

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- Extract Hatcher's degreewise cross-product isomorphism with the specified
native cup, rather than the provider's existential graded-ring operation.
Source: Theorem 3.15 pp.214–216. The provider's universal cocycle formula and
quotient surjectivity identify the two products on every pair of classes. -/
theorem kunneth_with_specified_cup (X Y : TopCat)
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)]
    [Topology.CWComplex.Finite (Set.univ : Set X)]
    [Topology.CWComplex (Set.univ : Set Y)]
    [Topology.CWComplex.Finite (Set.univ : Set Y)]
    (hfree : ∀ q : ℕ, Module.Free ℚ (SingularCochain.cohomology ℚ Y q) ∧
      Module.Finite ℚ (SingularCochain.cohomology ℚ Y q))
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
    ∃ μ : SingularCochain.crossProductDegreeDomain ℚ X Y k ≃ₗ[ℚ]
        SingularCochain.cohomology ℚ (SingularCochain.crossProductSpace X Y) k,
      ∀ (i : {i : ℕ × ℕ // i.1 + i.2 = k})
        (a : SingularCochain.cohomology ℚ X i.val.1)
        (b : SingularCochain.cohomology ℚ Y i.val.2),
        μ (DirectSum.lof ℚ _ _ i (TensorProduct.tmul ℚ a b)) =
          cast (congrArg
            (fun j ↦ (SingularCochain.cohomology ℚ
              (SingularCochain.crossProductSpace X Y) j : Type)) i.property)
            (cup i.val.1 i.val.2
              ((SingularCochain.cohomologyPullback ℚ
                (SingularCochain.crossProductFst X Y) i.val.1).hom a)
              ((SingularCochain.cohomologyPullback ℚ
                (SingularCochain.crossProductSnd X Y) i.val.2).hom b)) := by
  obtain ⟨G, hG, hK⟩ :=
    SingularCochain.finite_cw_cohomology_cross_product_kunneth ℚ X Y hfree
  have := G X
  have := G Y
  have := G (SingularCochain.crossProductSpace X Y)
  obtain ⟨AX, AY, AP, hdegree, _⟩ := hK
  obtain ⟨μ, hμ⟩ := hdegree k
  refine ⟨μ, ?_⟩
  intro i a b
  rw [hμ]
  congr 1
  exact graded_mul_eq_specified_cup _ _ cup hcup
    (hG (SingularCochain.crossProductSpace X Y)).1 _ _ _ _



end HolomorphicAnosov.TorusRationalCupBasisKronecker

