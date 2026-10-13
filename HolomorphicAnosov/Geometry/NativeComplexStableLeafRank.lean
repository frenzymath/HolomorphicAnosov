import HolomorphicAnosov.Geometry.NativeComplexStableLeafDatum
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! This file proves that the stable tangent fibres of a complex stable-leaf family have complex
dimension one. (Ghys, §2, pp. 588–589; Zhang, Lemma 2.5, p. 8) -/

open scoped ContDiff Manifold
namespace HolomorphicAnosov
universe u

/-- The tangent fibre of a complex rank-one stable-leaf family has complex dimension one at every
ambient point. (Ghys, §2, pp. 588–589; Zhang, Lemma 2.5, p. 8) -/
theorem NativeComplexStableLeafDatum.finrank
    {d : ℕ} {M : Type u} [MetricSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {f : M ≃ₜ M} {S : ContinuousComplexTangentSubbundle (complexModel d) M}
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    (F : NativeComplexStableLeafDatum f S ι L) (x : M) :
    Module.finrank ℂ (S.toDistribution x) = 1 := by
  obtain ⟨i, z, rfl⟩ := F.partition.cover x
  let := (F.complexUpgrade i).charts
  let := (F.complexUpgrade i).complex_manifold
  rw [← F.complex_tangent i z]
  rw [LinearMap.finrank_range_of_inj
    ((F.complexUpgrade i).inclusion_immersion z |>.mfderiv_injective (by simp))]
  change Module.finrank ℂ (Fin 1 → ℂ) = 1
  exact Module.finrank_fin_fun ℂ

end HolomorphicAnosov
