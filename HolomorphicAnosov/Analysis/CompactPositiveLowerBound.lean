import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace HolomorphicAnosov.Analysis

/-- A continuous strictly positive real function on a nonempty compact set has
 a positive uniform lower bound. -/
theorem exists_pos_lower_bound_of_isCompact
    {X : Type*} [TopologicalSpace X] (K : Set X) (hK : IsCompact K)
    (hne : K.Nonempty) (φ : X → ℝ) (hφ : ContinuousOn φ K)
    (hpos : ∀ x ∈ K, 0 < φ x) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ φ x := by
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hφ
  exact ⟨φ x, hpos x hx, fun y hy ↦ hmin hy⟩

/-- A continuous positive function homogeneous under real scaling has a uniform
linear lower bound when its unit-sphere restriction is compact. -/
theorem exists_uniform_linear_lower_bound_of_compact_homogeneous
    {X V : Type*} [TopologicalSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V] [CompactSpace X] [Nonempty X]
    (φ : X → V → ℝ)
    (hφ : Continuous (fun z : X × V ↦ φ z.1 z.2))
    (hpos : ∀ x v, ‖v‖ = 1 → 0 < φ x v)
    (hhom : ∀ x (c : ℝ) v, φ x (c • v) = |c| * φ x v) :
    ∃ m : ℝ, 0 < m ∧ ∀ x v, m * ‖v‖ ≤ φ x v := by
  let S : Set (X × V) := Set.univ ×ˢ Metric.sphere (0 : V) 1
  have hScompact : IsCompact S := by
    exact isCompact_univ.prod (isCompact_sphere (0 : V) 1)
  have hSne : S.Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨v, hv⟩ := exists_norm_ne_zero V
    let w : V := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := by simp [w, norm_smul, hv]
    exact ⟨(x, w), by simp [S, hw]⟩
  let ψ : X × V → ℝ := fun z ↦ φ z.1 z.2
  have hψ : ContinuousOn ψ S := hφ.continuousOn
  have hψpos : ∀ z ∈ S, 0 < ψ z := by
    intro z hz
    exact hpos z.1 z.2 (by simpa [S] using hz.2)
  obtain ⟨m, hm, hmS⟩ := exists_pos_lower_bound_of_isCompact S hScompact hSne ψ hψ hψpos
  refine ⟨m, hm, ?_⟩
  intro x v
  by_cases hv : v = 0
  · have hz := hhom x 0 v
    have hzero : φ x 0 = 0 := by simpa using hz
    simp [hv, hzero]
  let w : V := ‖v‖⁻¹ • v
  have hnorm : ‖w‖ = 1 := by
    simp [w, norm_smul, hv]
  have hw : (x, w) ∈ S := by simp [S, hnorm]
  have hbound : m ≤ φ x w := hmS (x, w) hw
  have hscaled := hhom x ‖v‖ w
  have hrew : ‖v‖ • w = v := by
    simp [w, hv]
  rw [hrew] at hscaled
  calc
    m * ‖v‖ = ‖v‖ * m := mul_comm _ _
    _ ≤ ‖v‖ * φ x w := mul_le_mul_of_nonneg_left hbound (norm_nonneg v)
    _ = φ x v := by simpa [abs_of_nonneg (norm_nonneg v)] using hscaled.symm

end HolomorphicAnosov.Analysis

