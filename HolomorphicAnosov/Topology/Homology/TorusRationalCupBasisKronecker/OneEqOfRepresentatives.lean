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
/-- The literal constant-one cochain determines a unique cohomology unit. -/
theorem one_eq_of_representatives (X : TopCat)
    (u v : SingularCochain.cohomology ℚ X 0)
    (hu : ∃ h : SingularCochain.oneCochain ℚ X ∈
        SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) 0,
      u = SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) 0
        ⟨SingularCochain.oneCochain ℚ X, h⟩)
    (hv : ∃ h : SingularCochain.oneCochain ℚ X ∈
        SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) 0,
      v = SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) 0
        ⟨SingularCochain.oneCochain ℚ X, h⟩) : u = v := by
  obtain ⟨_, rfl⟩ := hu
  obtain ⟨_, rfl⟩ := hv
  rfl
end HolomorphicAnosov.TorusRationalCupBasisKronecker
