import HolomorphicAnosov.Geometry.NativeLeafComplexUpgrade
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle

namespace HolomorphicAnosov
open scoped ContDiff Manifold
universe u v
attribute [local instance] complex_isManifold_real

/-- The realified fibre equality in the Demailly provider implies that each immersion derivative range is invariant under the ambient complex structure, transported from the complex tangent fibre by `complexTangentToReal`. -/
theorem mfderiv_range_complexTangent_invariant_of_complex_tangent
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin (2*k) → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (inc : L → M)
    (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    (hS : ∀ x : L, ((S.toDistribution (inc x)).restrictScalars ℝ).map
      (complexTangentToReal d (inc x)).toLinearEquiv.toLinearMap =
      (mfderiv 𝓘(ℝ, Fin (2*k) → ℝ) (realModel d) inc x).range) :
    ∀ x : L, ∀ v ∈ (mfderiv 𝓘(ℝ, Fin (2*k) → ℝ) (realModel d) inc x).range,
      (complexTangentToReal d (inc x))
        (Complex.I • (complexTangentToReal d (inc x)).symm v) ∈
      (mfderiv 𝓘(ℝ, Fin (2*k) → ℝ) (realModel d) inc x).range := by
  intro x v hv
  rw [← hS x] at hv ⊢
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
  refine Submodule.mem_map.mpr ⟨Complex.I • w, ?_, ?_⟩
  · exact Submodule.smul_mem _ Complex.I hw
  · simp

end HolomorphicAnosov
