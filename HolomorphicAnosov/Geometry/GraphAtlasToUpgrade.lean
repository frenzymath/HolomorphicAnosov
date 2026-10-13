import HolomorphicAnosov.Geometry.NativeLeafComplexUpgrade
import HolomorphicAnosov.Geometry.GraphAtlasGluing

namespace HolomorphicAnosov
open scoped ContDiff Manifold
universe u v
attribute [local instance] complex_isManifold_real

/-- A glued graph atlas with holomorphic, immersive inclusion defines a `NativeLeafComplexUpgrade`
on the given leaf carrier. -/
theorem native_leaf_graph_atlas_to_complex_upgrade
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : L → M)
    (A : NativeLeafGraphAtlas (k := k) (d := d) inc)
    (hhol : letI := A.charts
      ContMDiff (complexModel k) (complexModel d) ∞ inc)
    (himm : letI := A.charts
      ∀ z : L, Manifold.IsImmersionAt (complexModel k) (complexModel d) ∞ inc z) :
    Nonempty (NativeLeafComplexUpgrade (d := d) (r := 2*k) k inc) := by
  let := A.charts
  let := A.complex_manifold
  refine ⟨{
    real_rank := rfl
    charts := A.charts
    complex_manifold := A.complex_manifold
    real_to_complex := A.real_to_complex
    complex_to_real := A.complex_to_real
    inclusion_holomorphic := hhol
    inclusion_immersion := himm
  }⟩

end HolomorphicAnosov
