import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact

namespace HolomorphicAnosov.Analysis

/-- A continuous real coefficient on a compact set has a finite nonnegative
uniform absolute-value bound. This is the compact coefficient estimate used in
Ghys Lemma 3.2, p.591, for the quadratic section coefficient A(z,t). -/
theorem exists_abs_upper_bound_of_isCompact
    {X : Type*} [TopologicalSpace X] (K : Set X) (hK : IsCompact K)
    (φ : X → ℝ) (hφ : ContinuousOn φ K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, |φ x| ≤ M := by
  by_cases hne : K.Nonempty
  · have habs : ContinuousOn (fun x ↦ |φ x|) K :=
      continuous_abs.continuousOn.comp hφ (fun _ _ ↦ Set.mem_univ _)
    obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne habs
    exact ⟨|φ x|, abs_nonneg _, fun y hy ↦ hmax hy⟩
  · exact ⟨0, le_rfl, fun x hx ↦ (hne ⟨x, hx⟩).elim⟩

end HolomorphicAnosov.Analysis

