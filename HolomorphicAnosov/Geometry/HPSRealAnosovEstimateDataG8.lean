import HolomorphicAnosov.Dynamics.Anosov.InvariantRealTangentSplitting
import HolomorphicAnosov.Geometry.Manifold.Diffeomorph.RealIterate
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-! This file defines the original real tangent Anosov estimates and their existence predicate. -/



namespace HolomorphicAnosov

open scoped ContDiff Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- All-iterate Anosov estimates in the norms of the original supplied smooth real tangent tensor. The stable estimate is forward and the unstable estimate is inverse; the metric on each receiving vector is evaluated at that actual iterate image. (Zhang, p. 1; HPS, (2.8)–(2.9).) -/
structure TensorAnosovBounds (f : Diffeomorph I I M M ∞)
    (S : InvariantRealTangentSplitting f)
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) where
  C : ℝ
  lambda : ℝ
  C_pos : 0 < C
  lambda_pos : 0 < lambda
  lambda_lt_one : lambda < 1
  stable : ∀ (n : ℕ) (x : M) (v : TangentSpace I x),
    v ∈ S.stable.toDistribution x →
    Real.sqrt (g.inner (realIterate I f n x)
      (mfderiv I I (realIterate I f n) x v) (mfderiv I I (realIterate I f n) x v)) ≤
      C * lambda ^ n * Real.sqrt (g.inner x v v)
  unstable : ∀ (n : ℕ) (x : M) (v : TangentSpace I x),
    v ∈ S.unstable.toDistribution x →
    Real.sqrt (g.inner (realIterate I f.symm n x)
      (mfderiv I I (realIterate I f.symm n) x v)
      (mfderiv I I (realIterate I f.symm n) x v)) ≤
      C * lambda ^ n * Real.sqrt (g.inner x v v)

/-- Existence of constants for the same original all-iterate estimates, using the already supplied compatible Riemannian fibre norms. The `RiemannianBundle` instance fixes those norms on the existing tangent-fibre topologies. (Zhang, p. 1; HPS, (2.8)–(2.9).) -/
def BundleAnosovBounds (f : Diffeomorph I I M M ∞)
    (S : InvariantRealTangentSplitting f)
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)] : Prop :=
  ∃ C : ℝ, ∃ lambda : ℝ, 0 < C ∧ 0 < lambda ∧ lambda < 1 ∧
    (∀ (n : ℕ) (x : M) (v : TangentSpace I x), v ∈ S.stable.toDistribution x →
      ‖mfderiv I I (realIterate I f n) x v‖ ≤ C * lambda ^ n * ‖v‖) ∧
    (∀ (n : ℕ) (x : M) (v : TangentSpace I x), v ∈ S.unstable.toDistribution x →
      ‖mfderiv I I (realIterate I f.symm n) x v‖ ≤ C * lambda ^ n * ‖v‖)

end HolomorphicAnosov
