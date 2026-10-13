import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Algebra.Module.Equiv
import HolomorphicAnosov.Dynamics.Anosov.IterateInvariant

/-!
# Restricted iterate derivatives

Zhang, *Codimension-one holomorphic Anosov diffeomorphisms*, p.1, uses the
derivative restricted to an invariant real tangent subbundle and its inverse.
This construction restricts the actual derivative equivalence to its invariant
fibres. It uses their existing topologies and selects no tangent norms.
-/

namespace HolomorphicAnosov

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- The actual iterate derivative restricted to invariant real tangent fibres,
as required by the Anosov bounds in Zhang, p.1.

The forward map is the derivative of `realIterate I g n` on the source subtype.
Iterated invariance gives its exact target submodule. Mathlib's `ofSubmodules`
restricts the derivative equivalence and its canonical inverse, so the inverse
has source `P ((g^[n]) x)` and target `P x`. The only postponed proof used by
this construction is the named theorem `real_distribution_iterate_invariant`.
No norm, arbitrary linear equivalence, or inverse with a zero fallback is chosen. -/
noncomputable def restrictedIterateDerivative
    (g : Diffeomorph I I X X ∞) (P : RealTangentDistribution I X)
    (hP : ∀ x, (P x).map (mfderiv I I g x).toLinearMap = P (g x))
    (n : ℕ) (x : X) :
    ↥(P x) ≃L[ℝ] ↥(P (((g : X → X)^[n]) x)) :=
  ((realIterate I g n).mfderivToContinuousLinearEquiv (by simp) x).ofSubmodules
    (P x) (P (((g : X → X)^[n]) x))
    (real_distribution_iterate_invariant g P hP n x)

end HolomorphicAnosov
