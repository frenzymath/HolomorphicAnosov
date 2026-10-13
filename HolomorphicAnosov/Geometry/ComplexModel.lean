import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic




/-! This file defines the finite-dimensional complex coordinate model and its real and complex manifold models.
-/
namespace HolomorphicAnosov

noncomputable section

abbrev ComplexModel (d : ℕ) := Fin d → ℂ

abbrev complexModel (d : ℕ) :
    ModelWithCorners ℂ (ComplexModel d) (ComplexModel d) :=
  modelWithCornersSelf ℂ (ComplexModel d)

abbrev realModel (d : ℕ) :
    ModelWithCorners ℝ (ComplexModel d) (ComplexModel d) :=
  modelWithCornersSelf ℝ (ComplexModel d)

end
end HolomorphicAnosov
