import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Category.TopCat.Basic

open CategoryTheory
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- The literal coordinate inclusion with every other coordinate equal to zero. -/
def coordinateInclusion (n : ℕ) (i : Fin n) :
    TopCat.of UnitAddCircle ⟶ TopCat.of (UnitAddTorus (Fin n)) :=
  TopCat.ofHom ⟨fun x j ↦ if j = i then x else 0,
    continuous_pi fun j ↦ by split_ifs <;> fun_prop⟩

end HolomorphicAnosov.TorusRationalCupBasisKronecker
