import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle

/-!
# Invariant real tangent splittings

Zhang, *Codimension-one holomorphic Anosov diffeomorphisms*, p.1, uses a
continuous invariant splitting of the real tangent bundle. This structure
records its subbundles, complementarity, and exact derivative image equalities.
Metric and contraction conditions are separate Anosov data.
-/

namespace HolomorphicAnosov

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- An invariant complementary continuous real tangent splitting, as used in Zhang, p.1.

Invariance is equality of each fibre's image under the actual manifold derivative
with the corresponding fibre at the image point. No rank, metric, contraction,
complex invariance, or holomorphicity condition is imposed here. -/
structure InvariantRealTangentSplitting (g : Diffeomorph I I X X ∞) where
  /-- The stable real tangent subbundle. -/
  stable : ContinuousRealTangentSubbundle I X
  /-- The unstable real tangent subbundle. -/
  unstable : ContinuousRealTangentSubbundle I X
  /-- The two fibres form a direct-sum decomposition of each real tangent space. -/
  isCompl : ∀ x, IsCompl (stable.toDistribution x) (unstable.toDistribution x)
  /-- The derivative maps the stable fibre exactly onto the next stable fibre. -/
  stable_map : ∀ x,
    (stable.toDistribution x).map (mfderiv I I g x).toLinearMap =
      stable.toDistribution (g x)
  /-- The derivative maps the unstable fibre exactly onto the next unstable fibre. -/
  unstable_map : ∀ x,
    (unstable.toDistribution x).map (mfderiv I I g x).toLinearMap =
      unstable.toDistribution (g x)

end HolomorphicAnosov
