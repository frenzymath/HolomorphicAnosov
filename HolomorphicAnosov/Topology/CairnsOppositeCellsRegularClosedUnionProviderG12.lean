import Mathlib.Analysis.Complex.Circle
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded
import HolomorphicAnosov.Topology.OppositeHalfPlanesClosureUnion

namespace HolomorphicAnosov
open Set

/-- Cairns preliminary 2(B), p.860: opposite bounded complementary cells
have a compact connected regular-closed union whose interior contains the
seam. This provider isolates the local closure-cover argument. -/
theorem cairns_opposite_cells_regular_closed_union_provider
    {n₁ n₂ : ℕ} (q₁ : Polygon ℂ (n₁ + 3)) (q₂ : Polygon ℂ (n₂ + 3))
    (_hq₁_ambient : ∃ F : ℂ ≃ₜ ℂ, F '' q₁.boundary ℝ = Metric.sphere (0 : ℂ) 1)
    (_hq₂_ambient : ∃ F : ℂ ≃ₜ ℂ, F '' q₂.boundary ℝ = Metric.sphere (0 : ℂ) 1)
    (u₁ u₂ : ℂ) (_hu₁ : u₁ ∉ q₁.boundary ℝ) (_hu₂ : u₂ ∉ q₂.boundary ℝ)
    (C₁ C₂ : Set ℂ)
    (_hC₁ : C₁ = connectedComponentIn (q₁.boundary ℝ)ᶜ u₁)
    (_hC₂ : C₂ = connectedComponentIn (q₂.boundary ℝ)ᶜ u₂)
    (_hC₁_bounded : Bornology.IsBounded C₁) (_hC₂_bounded : Bornology.IsBounded C₂)
    (a b : ℂ) (_hab : a ≠ b)
    (_hD_inter : closure C₁ ∩ closure C₂ = segment ℝ a b)
    (h_opposite : ∀ x ∈ openSegment ℝ a b, ∃ ε : ℝ, 0 < ε ∧
      ∃ ν : ℂ, ‖ν‖ = 1 ∧ ((b - a) / ν).re = 0 ∧
        Metric.ball x ε ∩ C₁ = {z : ℂ | z ∈ Metric.ball x ε ∧ 0 < ((z - x) / ν).re} ∧
        Metric.ball x ε ∩ C₂ = {z : ℂ | z ∈ Metric.ball x ε ∧ ((z - x) / ν).re < 0}) :
    openSegment ℝ a b ⊆ interior (closure C₁ ∪ closure C₂) := by
  intro x hx
  obtain ⟨ε, hε, ν, hν, hperp, h₁, h₂⟩ := h_opposite x hx
  have hν0 : ν ≠ 0 := by intro hz; simp [hz] at hν
  have hcover : Metric.ball x ε ⊆ closure C₁ ∪ closure C₂ := by
    apply opposite_half_planes_closure_union (Metric.ball x ε) C₁ C₂
      Metric.isOpen_ball x ν hν0
    · exact h₁
    · exact h₂
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (Metric.ball_mem_nhds x hε) hcover

end HolomorphicAnosov

