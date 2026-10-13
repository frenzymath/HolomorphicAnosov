import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
namespace HolomorphicAnosov
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- The `n`-fold iterate of the inverse of a diffeomorphism undoes its `n`-fold forward iterate. -/
theorem inverse_iterate_basepoint (g : Diffeomorph I I X X ∞) (n : ℕ) (x : X) :
    ((g.symm : X → X)^[n]) (((g : X → X)^[n]) x) = x :=
  g.left_inv.iterate n x

end HolomorphicAnosov
