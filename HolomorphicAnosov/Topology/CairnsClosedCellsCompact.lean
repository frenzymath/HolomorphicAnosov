import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Homeomorph.Lemmas

open Set Metric

namespace HolomorphicAnosov.Topology

/-- Two closed-cell disk charts make the union of the carriers compact and closed.

Source: the compactness step in Cairns (1951), §4(D), equation (4.5),
printed pp.865–866. Each closed cell is homeomorphic to the compact closed unit
disk, so each is compact; their finite union is compact, and compact subsets of
the Hausdorff complex plane are closed. -/
theorem cairns_closed_cells_compact_closed
    (K₁ K₂ : Set ℂ)
    (H₁ : K₁ ≃ₜ closedBall (0 : ℂ) 1)
    (H₂ : K₂ ≃ₜ closedBall (0 : ℂ) 1) :
    IsCompact (K₁ ∪ K₂) ∧ IsClosed (K₁ ∪ K₂) := by
  have cell_compact (K : Set ℂ) (H : K ≃ₜ closedBall (0 : ℂ) 1) :
      IsCompact K := by
    have hi : IsCompact (H.symm '' (Set.univ : Set (closedBall (0 : ℂ) 1))) :=
      isCompact_univ.image H.symm.continuous
    have him : H.symm '' (Set.univ : Set (closedBall (0 : ℂ) 1)) = Set.univ := by
      ext z
      constructor
      · intro _
        trivial
      · intro _
        exact ⟨H z, trivial, H.symm_apply_apply z⟩
    rw [him] at hi
    have hs : IsCompact (Set.univ : Set K) := by
      rw [Subtype.isCompact_iff]
      exact Subtype.isCompact_iff.mp hi
    exact isCompact_iff_isCompact_univ.mpr hs
  have hK₁ := cell_compact K₁ H₁
  have hK₂ := cell_compact K₂ H₂
  exact ⟨hK₁.union hK₂, (hK₁.union hK₂).isClosed⟩

end HolomorphicAnosov.Topology
