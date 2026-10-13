import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic

open Set Metric

namespace HolomorphicAnosov.Topology

/-- The seam union and outer boundary of two cells lie in their closed-cell union.

Source: elementary set-theoretic step in Cairns (1951), §4(D), equation (4.5),
printed pp.865–866. The displayed closure identities `closure Uᵢ = Uᵢ ∪ cᵢ`
and the inclusion of the common arc in each boundary imply both containments.
No separation or curve theorem is used. -/
theorem cairns_seam_subset_closed_cells
    (U₁ U₂ c₁ c₂ B : Set ℂ) (p q : ℂ)
    (hclosure₁ : closure U₁ = U₁ ∪ c₁)
    (hclosure₂ : closure U₂ = U₂ ∪ c₂)
    (hproper₁ : B ⊆ c₁ ∧ B ≠ c₁) :
    let R : Set ℂ := U₁ ∪ U₂ ∪ (B \ {p, q})
    let C : Set ℂ := (c₁ ∪ c₂) \ (B \ {p, q})
    R ⊆ closure U₁ ∪ closure U₂ ∧ C ⊆ closure U₁ ∪ closure U₂ := by
  let R : Set ℂ := U₁ ∪ U₂ ∪ (B \ {p, q})
  let C : Set ℂ := (c₁ ∪ c₂) \ (B \ {p, q})
  constructor
  · intro z hz
    rcases hz with hz | hz
    · rcases hz with hz | hz
      · exact Or.inl (subset_closure hz)
      · exact Or.inr (subset_closure hz)
    · left
      rw [hclosure₁]
      exact Or.inr (hproper₁.1 hz.1)
  · intro z hz
    rcases hz.1 with hz | hz
    · left
      rw [hclosure₁]
      exact Or.inr hz
    · right
      rw [hclosure₂]
      exact Or.inr hz

end HolomorphicAnosov.Topology
