import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.ComplexImmersionGraphCharts
import HolomorphicAnosov.Geometry.ComplexDifferentialImmersionOfInjectiveDerivative
import Mathlib.Geometry.Manifold.Immersion




/-! This file proves the local immersion theorem for holomorphic maps with injective complex derivative. (Demailly, I.7.15, p. 60).
-/
namespace HolomorphicAnosov
open scoped ContDiff Manifold
universe u v

/-- A holomorphic map between finite-dimensional complex manifolds is an immersion at a point when its complex derivative there is injective. (Demailly, I.7.15, p. 60). -/
theorem complex_holomorphic_immersion_of_injective_derivative
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (ComplexModel k) L]
    [IsManifold (complexModel k) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {f : L → M} {x : L}
    (hf : ContMDiffAt (complexModel k) (complexModel d) ∞ f x)
    (hinj : Function.Injective (mfderiv (complexModel k) (complexModel d) f x)) :
    Manifold.IsImmersionAt (complexModel k) (complexModel d) ∞ f x := by
  obtain ⟨F, e, a, b, hx, hfx, ha, hb, hab, heq⟩ :=
    complex_immersion_graph_charts hf
      (complex_differential_immersion_of_injective_derivative hf hinj)
  exact Manifold.IsImmersionAt.mk_of_charts e a b hx hfx ha hb hab heq

end HolomorphicAnosov

