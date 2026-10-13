import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Geometry.Manifold.ImmersionDiff




/-! This file derives a differential immersion from injectivity of a complex derivative. (Mathlib, `IsDiffImmersionAt.of_injective_of_finiteDimensional`).
-/
namespace HolomorphicAnosov
open scoped ContDiff Manifold
universe u v

/-- An injective derivative into a finite-dimensional complex model implies a differential immersion at the point. (Mathlib, `IsDiffImmersionAt.of_injective_of_finiteDimensional`). -/
theorem complex_differential_immersion_of_injective_derivative
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (ComplexModel k) L]
    [IsManifold (complexModel k) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {f : L → M} {x : L}
    (_hf : ContMDiffAt (complexModel k) (complexModel d) ∞ f x)
    (hinj : Function.Injective (mfderiv (complexModel k) (complexModel d) f x)) :
    IsDiffImmersionAt (complexModel k) (complexModel d) f x := by
  exact IsDiffImmersionAt.of_injective_of_finiteDimensional hinj

end HolomorphicAnosov

