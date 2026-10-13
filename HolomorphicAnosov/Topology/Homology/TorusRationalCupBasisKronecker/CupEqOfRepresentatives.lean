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
/-- A bilinear operation on original singular cohomology is uniquely determined by its
values on cocycle representatives. Quotient surjectivity in each variable proves equality
on all classes; the two witnesses that the cup cochain is closed agree by proof irrelevance.
This is the operation-identification step in the source Künneth induction. -/
theorem cup_eq_of_representatives (X : TopCat) (p q : ℕ)
    (μ ν : SingularCochain.cohomology ℚ X p →ₗ[ℚ]
      SingularCochain.cohomology ℚ X q →ₗ[ℚ]
        SingularCochain.cohomology ℚ X (p + q))
    (hμ : ∀ (b : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) p)
        (c : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) q),
      ∃ hc : SingularCochain.cupCochain ℚ X b.val c.val ∈
          SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) (p + q),
        μ (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p b)
            (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) q c) =
          SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) (p + q)
            ⟨SingularCochain.cupCochain ℚ X b.val c.val, hc⟩)
    (hν : ∀ (b : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) p)
        (c : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) q),
      ∃ hc : SingularCochain.cupCochain ℚ X b.val c.val ∈
          SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) (p + q),
        ν (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p b)
            (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) q c) =
          SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) (p + q)
            ⟨SingularCochain.cupCochain ℚ X b.val c.val, hc⟩) : μ = ν := by
  have hp : Function.Surjective
      (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p) :=
    Submodule.mkQ_surjective _
  have hq : Function.Surjective
      (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) q) :=
    Submodule.mkQ_surjective _
  ext a b
  obtain ⟨c, rfl⟩ := hp a
  obtain ⟨d, rfl⟩ := hq b
  obtain ⟨hc, heμ⟩ := hμ c d
  obtain ⟨hd, heν⟩ := hν c d
  exact heμ.trans heν.symm
end HolomorphicAnosov.TorusRationalCupBasisKronecker
