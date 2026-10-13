import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.RealTangentDistribution

/-!
A diffeomorphism transports a real tangent distribution by its derivative.
-/

namespace HolomorphicAnosov.Theorem12SupportW4

open scoped Bundle ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace K N]

/-- The tangent distribution whose fibre at `y` is the image of `P (e.symm y)` under the derivative
of `e` at `e.symm y`. -/
noncomputable def rechartDistribution (e : Diffeomorph I J M N ∞)
    (P : RealTangentDistribution I M) : RealTangentDistribution J N :=
  fun y ↦ (P (e.symm y)).map (mfderiv I J e (e.symm y)).toLinearMap

end HolomorphicAnosov.Theorem12SupportW4
