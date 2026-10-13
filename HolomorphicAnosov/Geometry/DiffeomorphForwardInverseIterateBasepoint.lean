import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
namespace HolomorphicAnosov
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- The `n`th forward iterate of a diffeomorphism cancels its `n`th inverse iterate at every point. -/
theorem forward_iterate_inverse_basepoint (g : Diffeomorph I I X X ∞) (n : ℕ) (x : X) :
    ((g : X → X)^[n]) (((g.symm : X → X)^[n]) x) = x :=
  g.right_inv.iterate n x

end HolomorphicAnosov
