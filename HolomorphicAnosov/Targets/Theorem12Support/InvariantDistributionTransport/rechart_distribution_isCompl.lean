import HolomorphicAnosov.Targets.Theorem12Support.InvariantDistributionTransport.rechartDistribution
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Algebra.Module.Submodule.Range

/-!
The derivative of a diffeomorphism preserves complementary tangent distributions.
-/

namespace HolomorphicAnosov.Theorem12SupportW4
open scoped Bundle ContDiff
section Rechart
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace K N]

/-- Transport by a smooth diffeomorphism preserves fibrewise complementarity of real tangent
distributions. -/

theorem rechart_distribution_isCompl (e : Diffeomorph I J M N ∞)
    (S U : RealTangentDistribution I M) (hSU : ∀ x, IsCompl (S x) (U x)) (y : N) :
    IsCompl (rechartDistribution e S y) (rechartDistribution e U y) := by
  have hi := Submodule.isCompl_map
    (e.mfderivToContinuousLinearEquiv (by simp) (e.symm y)).toLinearEquiv (hSU (e.symm y))
  exact hi


end Rechart
end HolomorphicAnosov.Theorem12SupportW4
