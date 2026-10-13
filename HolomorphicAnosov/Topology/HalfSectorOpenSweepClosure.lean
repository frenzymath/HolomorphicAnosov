import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Topology

/-!
# Closure of the radial sweep over a compact front

Agent-written expansion of the radial-sweep closure step in Cairns (1951),
§3(E), p.863 and §4(A), pp.863–864. The front must be compact: without it,
limits of front points can add missing radial segments. The result includes
an empty front and fronts containing the apex.
-/
namespace HolomorphicAnosov
open Set

/-- Over a compact complex front, the closure of the union of open radial
segments is exactly the union of the corresponding closed segments.

Proof: the closed sweep is the continuous image of the compact product
`[0,1] × L`, hence closed. It contains every open segment, giving one inclusion.
For the reverse inclusion, fix a front point and use that its closed segment
is contained in the closure of its open segment, then apply closure monotonicity.
This does not distribute closure over an infinite union. -/
theorem halfSector_openSweep_closure_of_compact
    (M : ℂ) (L : Set ℂ) (hL : IsCompact L) :
    closure (⋃ Q ∈ L, openSegment ℝ M Q) = ⋃ Q ∈ L, segment ℝ M Q := by
  have hImage : (⋃ Q ∈ L, segment ℝ M Q) =
      (fun p : ℝ × ℂ ↦ (1 - p.1) • M + p.1 • p.2) '' (Icc 0 1 ×ˢ L) := by
    ext x
    simp only [mem_iUnion, segment_eq_image, mem_image, Prod.exists,
      mem_prod]
    constructor
    · rintro ⟨Q, hQ, t, ht, heq⟩
      exact ⟨t, Q, ⟨ht, hQ⟩, heq⟩
    · rintro ⟨t, Q, ⟨ht, hQ⟩, heq⟩
      exact ⟨Q, hQ, t, ht, heq⟩
  have hClosed : IsClosed (⋃ Q ∈ L, segment ℝ M Q) := by
    rw [hImage]
    exact (((ConditionallyCompleteLinearOrder.isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod hL).image (by fun_prop)).isClosed
  apply Subset.antisymm
  · apply closure_minimal _ hClosed
    exact iUnion₂_mono fun Q _ ↦ openSegment_subset_segment ℝ M Q
  · refine iUnion₂_subset fun Q hQ ↦ ?_
    exact segment_subset_closure_openSegment.trans
      (closure_mono (subset_iUnion₂_of_subset Q hQ Subset.rfl))

end HolomorphicAnosov
