import Mathlib.Geometry.Manifold.Diffeomorph

/-! Conjugation by a smooth diffeomorphism gives a smooth diffeomorphism on the target manifold.
(Zhang, Theorem 1.2) -/

open scoped ContDiff Manifold

namespace HolomorphicAnosov.Theorem12SupportW2

noncomputable section

universe u v

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace K N]
  (e : Diffeomorph I J M N ∞)

/-- The smooth diffeomorphism `e ∘ f ∘ e⁻¹` on the target manifold. (Zhang, Theorem 1.2) -/
def conjugatedDiffeomorph (f : Diffeomorph I I M M ∞) : Diffeomorph J J N N ∞ :=
  (e.symm.trans f).trans e


end
end HolomorphicAnosov.Theorem12SupportW2
