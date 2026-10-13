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
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularPullbackComp
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularPullbackId

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- A homeomorphism transports the literal singular cohomology quotient by its
actual contravariant pullback. Hatcher pp.201–202, used in the product splitting
of Example 3.16 p.216. Both inverse laws follow from functoriality, with no
cohomology classification assumption. -/
def singularPullbackHomeomorph {X Y : TopCat} (e : X ≃ₜ Y) (k : ℕ) :
    SingularCochain.cohomology ℚ Y k ≃ₗ[ℚ] SingularCochain.cohomology ℚ X k :=
  (show SingularCochain.cohomology ℚ Y k ≅ SingularCochain.cohomology ℚ X k from
    { hom := SingularCochain.cohomologyPullback ℚ (TopCat.isoOfHomeo e).hom k
      inv := SingularCochain.cohomologyPullback ℚ (TopCat.isoOfHomeo e).inv k
      hom_inv_id := by rw [← singularPullback_comp, Iso.inv_hom_id, singularPullback_id]
      inv_hom_id := by rw [← singularPullback_comp, Iso.hom_inv_id, singularPullback_id] }).toLinearEquiv


end HolomorphicAnosov.TorusRationalCupBasisKronecker

