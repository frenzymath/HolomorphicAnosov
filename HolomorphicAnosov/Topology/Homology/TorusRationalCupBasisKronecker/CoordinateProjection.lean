import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Category.TopCat.Basic

open CategoryTheory
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- The literal coordinate projection of the original quotient torus. -/
def coordinateProjection (n : ℕ) (i : Fin n) :
    TopCat.of (UnitAddTorus (Fin n)) ⟶ TopCat.of UnitAddCircle :=
  TopCat.ofHom ⟨fun x ↦ x i, continuous_apply i⟩

end HolomorphicAnosov.TorusRationalCupBasisKronecker
