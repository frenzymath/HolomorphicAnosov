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

/-- The graded multiplication selected by Künneth equals any supplied cup with
the same original cocycle formula. Hatcher pp.206–207 and Theorem 3.15 p.216.
Surjectivity of both cocycle quotient maps makes this an equality on all classes;
no ring structure is substituted on the original cohomology carrier. -/
theorem graded_mul_eq_specified_cup (X : TopCat)
    (G : DirectSum.GRing (fun k ↦ SingularCochain.cohomology ℚ X k))
    (cup : ∀ p q : ℕ, SingularCochain.cohomology ℚ X p →ₗ[ℚ]
      SingularCochain.cohomology ℚ X q →ₗ[ℚ] SingularCochain.cohomology ℚ X (p + q))
    (hcup : ∀ p q (b : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) p)
        (c : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) q),
      ∃ hc : SingularCochain.cupCochain ℚ X b.val c.val ∈
          SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) (p + q),
        cup p q (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p b)
          (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) q c) =
          SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) (p + q)
            ⟨SingularCochain.cupCochain ℚ X b.val c.val, hc⟩)
    (hG : letI := G
      ∀ p q (b : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) p)
        (c : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) q),
      ∃ hc : SingularCochain.cupCochain ℚ X b.val c.val ∈
          SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) (p + q),
        GradedMonoid.GMul.mul (A := fun k ↦ SingularCochain.cohomology ℚ X k)
          (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p b)
          (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) q c) =
          SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) (p + q)
            ⟨SingularCochain.cupCochain ℚ X b.val c.val, hc⟩) :
    letI := G
    ∀ p q (a : SingularCochain.cohomology ℚ X p)
      (b : SingularCochain.cohomology ℚ X q),
      GradedMonoid.GMul.mul (A := fun k ↦ SingularCochain.cohomology ℚ X k)
        a b = cup p q a b := by
  have := G
  intro p q a b
  obtain ⟨a', rfl⟩ := (show Function.Surjective
    (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p) from
    Submodule.mkQ_surjective _) a
  obtain ⟨b', rfl⟩ := (show Function.Surjective
    (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) q) from
    Submodule.mkQ_surjective _) b
  obtain ⟨ha, hGa⟩ := hG p q a' b'
  obtain ⟨hb, hca⟩ := hcup p q a' b'
  exact hGa.trans hca.symm


end HolomorphicAnosov.TorusRationalCupBasisKronecker

