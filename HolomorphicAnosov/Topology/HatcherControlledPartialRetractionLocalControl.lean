import HolomorphicAnosov.Topology.HatcherControlledPartialRetractionCellSelection

/-!
# Metric neighborhood control from Hatcher's selected subcomplex

The cell-selection module gives relative-open neighborhood control of the glued
map.  This module records the final metric conversion used in Hatcher's
Theorem A.7: specialize the relative neighborhood to an epsilon ball in the
compact carrier and read the ambient-ball and image-distance clauses.
-/

namespace HolomorphicAnosov

/-- Convert relative-open control of a glued map into Hatcher's metric estimate.

Source: Hatcher, *Algebraic Topology*, Theorem A.7, pp.525--526.  The proof
chooses the relative open ball of radius `ε` around `c`, applies the cell
selection's shrinking estimate, and unfolds membership in that ball as the
strict distance inequality.  The extension is still only required to be
continuous on `Z`; no continuity across the complement is introduced.
-/
theorem hatcher_controlled_partial_retraction_local_control
    (N : ℕ) (C : Set (EuclideanSpace ℝ (Fin N)))
    (Z : Set (EuclideanSpace ℝ (Fin N)))
    (r : EuclideanSpace ℝ (Fin N) → C)
    (_hcont : ContinuousOn r Z) (_hfix : ∀ c : C, r c = c)
    (hopen : ∀ c : C, ∀ V : Set C, IsOpen V → c ∈ V →
      ∃ δ : ℝ, 0 < δ ∧ Metric.ball c.val δ ⊆ Z ∪ C ∧
        ∀ z ∈ Z, dist z c.val < δ → r z ∈ V) :
    ∀ c : C, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      Metric.ball c.val δ ⊆ Z ∪ C ∧
      ∀ z ∈ Z, dist z c.val < δ → dist (r z).val c.val < ε := by
  intro c ε hε
  obtain ⟨δ, hδ, hball, hV⟩ :=
    hopen c (Metric.ball c ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
  refine ⟨δ, hδ, hball, ?_⟩
  intro z hz hdist
  have hzV : r z ∈ Metric.ball c ε := hV z hz hdist
  exact hzV


end HolomorphicAnosov
