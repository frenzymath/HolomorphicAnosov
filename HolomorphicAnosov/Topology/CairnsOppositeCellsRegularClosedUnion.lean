import Mathlib.Analysis.Complex.Circle
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import HolomorphicAnosov.Topology.CairnsOppositeCellsRegularClosedUnionProviderG12

namespace HolomorphicAnosov
open Set

/-- The bounded complementary components of two ambiently circular polygons are open; their
closures form a compact connected regular-closed union, and the prescribed opposite seam lies
in its interior. This is the local bounded-cell part of Cairns preliminary 2(B), p. 860. -/
theorem cairns_opposite_cells_regular_closed_union
    {n₁ n₂ : ℕ} (q₁ : Polygon ℂ (n₁ + 3)) (q₂ : Polygon ℂ (n₂ + 3))
    (hq₁_ambient : ∃ F : ℂ ≃ₜ ℂ, F '' q₁.boundary ℝ = Metric.sphere (0 : ℂ) 1)
    (hq₂_ambient : ∃ F : ℂ ≃ₜ ℂ, F '' q₂.boundary ℝ = Metric.sphere (0 : ℂ) 1)
    (u₁ u₂ : ℂ) (hu₁ : u₁ ∉ q₁.boundary ℝ) (hu₂ : u₂ ∉ q₂.boundary ℝ)
    (C₁ C₂ : Set ℂ)
    (hC₁ : C₁ = connectedComponentIn (q₁.boundary ℝ)ᶜ u₁)
    (hC₂ : C₂ = connectedComponentIn (q₂.boundary ℝ)ᶜ u₂)
    (hC₁_bounded : Bornology.IsBounded C₁) (hC₂_bounded : Bornology.IsBounded C₂)
    (a b : ℂ) (hab : a ≠ b)
    (hD_inter : closure C₁ ∩ closure C₂ = segment ℝ a b)
    (h_opposite : ∀ x ∈ openSegment ℝ a b, ∃ ε : ℝ, 0 < ε ∧
      ∃ ν : ℂ, ‖ν‖ = 1 ∧ ((b - a) / ν).re = 0 ∧
        Metric.ball x ε ∩ C₁ = {z : ℂ | z ∈ Metric.ball x ε ∧ 0 < ((z - x) / ν).re} ∧
        Metric.ball x ε ∩ C₂ = {z : ℂ | z ∈ Metric.ball x ε ∧ ((z - x) / ν).re < 0}) :
    IsOpen C₁ ∧ IsOpen C₂ ∧
    IsCompact (closure C₁ ∪ closure C₂) ∧
    IsConnected (closure C₁ ∪ closure C₂) ∧
    closure (interior (closure C₁ ∪ closure C₂)) = closure C₁ ∪ closure C₂ ∧
    (interior (closure C₁ ∪ closure C₂)).Nonempty ∧
    openSegment ℝ a b ⊆ interior (closure C₁ ∪ closure C₂) := by
  have hseam := cairns_opposite_cells_regular_closed_union_provider q₁ q₂ hq₁_ambient hq₂_ambient u₁ u₂ hu₁ hu₂ C₁ C₂ hC₁ hC₂ hC₁_bounded hC₂_bounded a b hab hD_inter h_opposite
  let : LocallyConnectedSpace ℂ := locallyConnectedSpace_of_connected_bases
    (fun x r ↦ Metric.ball x r) (fun _ r ↦ 0 < r)
    (fun _ ↦ Metric.nhds_basis_ball)
    (fun _ _ _ ↦ (convex_ball _ _).isPreconnected)
  obtain ⟨F₁, hF₁⟩ := hq₁_ambient
  obtain ⟨F₂, hF₂⟩ := hq₂_ambient
  have hbd₁ : IsClosed (q₁.boundary ℝ) := by
    rw [show q₁.boundary ℝ = F₁ ⁻¹' Metric.sphere (0 : ℂ) 1 by
      ext z
      constructor
      · intro hz
        rw [← hF₁]
        exact ⟨z, hz, rfl⟩
      · intro hz
        change F₁ z ∈ Metric.sphere (0 : ℂ) 1 at hz
        rw [← hF₁] at hz
        obtain ⟨w, hw, hwe⟩ := hz
        exact F₁.injective hwe ▸ hw]
    exact Metric.isClosed_sphere.preimage F₁.continuous
  have hbd₂ : IsClosed (q₂.boundary ℝ) := by
    rw [show q₂.boundary ℝ = F₂ ⁻¹' Metric.sphere (0 : ℂ) 1 by
      ext z
      constructor
      · intro hz
        rw [← hF₂]
        exact ⟨z, hz, rfl⟩
      · intro hz
        change F₂ z ∈ Metric.sphere (0 : ℂ) 1 at hz
        rw [← hF₂] at hz
        obtain ⟨w, hw, hwe⟩ := hz
        exact F₂.injective hwe ▸ hw]
    exact Metric.isClosed_sphere.preimage F₂.continuous
  have hopen₁ : IsOpen C₁ := by
    rw [hC₁]
    exact hbd₁.isOpen_compl.connectedComponentIn
  have hopen₂ : IsOpen C₂ := by
    rw [hC₂]
    exact hbd₂.isOpen_compl.connectedComponentIn
  have hconn₁ : IsConnected C₁ := by
    rw [hC₁]
    apply isConnected_connectedComponentIn_iff.mpr
    exact hu₁
  have hconn₂ : IsConnected C₂ := by
    rw [hC₂]
    apply isConnected_connectedComponentIn_iff.mpr
    exact hu₂
  have hcomp₁ : IsCompact (closure C₁) := hC₁_bounded.isCompact_closure
  have hcomp₂ : IsCompact (closure C₂) := hC₂_bounded.isCompact_closure
  have hcompact : IsCompact (closure C₁ ∪ closure C₂) := hcomp₁.union hcomp₂
  have hinter : (closure C₁ ∩ closure C₂).Nonempty := by
    rw [hD_inter]
    exact ⟨midpoint ℝ a b, midpoint_mem_segment (𝕜 := ℝ) a b⟩
  have hconnected : IsConnected (closure C₁ ∪ closure C₂) :=
    IsConnected.union hinter hconn₁.closure hconn₂.closure
  let U : Set ℂ := closure C₁ ∪ closure C₂
  have hUclosed : IsClosed U := isClosed_closure.union isClosed_closure
  have hleft : U ⊆ closure (interior U) := by
    apply union_subset
    · apply closure_mono
      exact (hopen₁.subset_interior_closure).trans (interior_mono (subset_union_left))
    · apply closure_mono
      exact (hopen₂.subset_interior_closure).trans (interior_mono (subset_union_right))
  have hright : closure (interior U) ⊆ U := closure_minimal interior_subset hUclosed
  have hregular : closure (interior U) = U := by
    exact le_antisymm hright hleft
  have hnonempty : (interior U).Nonempty := by
    exact ⟨midpoint ℝ a b, hseam (midpoint_mem_openSegment (𝕜 := ℝ) a b)⟩
  exact ⟨hopen₁, hopen₂, hcompact, hconnected, hregular, hnonempty, hseam⟩

end HolomorphicAnosov
