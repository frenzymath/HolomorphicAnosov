import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy

open CategoryTheory
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- The actual positive additive-circle loop used in the public theorem. -/
def additivePositiveLoop : TopCat.I ⟶ TopCat.of UnitAddCircle :=
  TopCat.ofHom ⟨fun t ↦ ((t.down : ℝ) : UnitAddCircle), by fun_prop⟩

end HolomorphicAnosov.TorusRationalCupBasisKronecker
