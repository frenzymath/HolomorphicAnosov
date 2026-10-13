import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Subpath

namespace HolomorphicAnosov
open Set

/-- The base segment between the two distinguished front points lies in the
closed radial sweep from their midpoint.

Source: Cairns (1951), §4(A), pp.863--864.  Split the base at its midpoint:
points on the first half are radial combinations of `N` and `E₁`, while points
on the second half are radial combinations of `N` and `E₂`. -/
theorem cairns_base_segment_subset_sweep
    (E₁ E₂ : ℂ) (ν : Set ℂ) (hE₁ : E₁ ∈ ν) (hE₂ : E₂ ∈ ν) :
    segment ℝ E₁ E₂ ⊆ {z : ℂ | ∃ Q ∈ ν, ∃ t ∈ Icc (0 : ℝ) 1,
      z = (1 - t) • ((E₁ + E₂) / 2) + t • (Q : ℂ)} := by
  rw [segment_eq_image ℝ E₁ E₂]
  rintro z ⟨s, hs, rfl⟩
  by_cases hhalf : s ≤ (1 / 2 : ℝ)
  · refine ⟨E₁, hE₁, 1 - 2 * s, ?_, ?_⟩
    · constructor
      · linarith [hs.1]
      · linarith [hs.1, hs.2]
    · dsimp
      push_cast
      ring
  · refine ⟨E₂, hE₂, 2 * s - 1, ?_, ?_⟩
    · constructor
      · linarith [hs.1, hhalf]
      · linarith [hs.2]
    · dsimp
      push_cast
      ring

end HolomorphicAnosov
