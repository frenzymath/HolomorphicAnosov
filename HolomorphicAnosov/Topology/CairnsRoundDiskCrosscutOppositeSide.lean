import HolomorphicAnosov.Topology.RoundDiskCrosscutGeometry
import HolomorphicAnosov.Topology.CairnsRoundDiskPolygonSeparator
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.UnitInterval

/-!
# Opposite-side provider for a round-disk crosscut

Source: Cairns (1951), Lemma 5.1, printed p.866, specifically the polygonal
crossing contradiction that distinguishes the two circle-side collar components.
This module isolates the first genuine separation conclusion used by the larger
round-disk crosscut theorem.
-/

open Set Metric

namespace HolomorphicAnosov

/-- An embedded crosscut of the round disk has points in distinct components of
its open-disk complement.  The source proof selects one inward collar on each
circle side and uses a polygonal approximation crossing the two sides.  The
remaining disk-cell and boundary-extension conclusions belong to the parent
provider.

The omitted source step is exactly Cairns's polygonal-path contradiction: if
both side collars belonged to one component, the polygon completion theorem
would provide a simple polygon meeting the circle once on each side; its
transverse radial edges force nearby points of one circle arc into opposite
polygon components, while the crosscut joins the marked endpoints away from
that polygon, a contradiction. -/
theorem cairns_round_disk_crosscut_opposite_side_provider
    (g : unitInterval → closedBall (0 : ℂ) 1) (hg : Topology.IsEmbedding g)
    (h0 : (g 0 : ℂ) ∈ sphere (0 : ℂ) 1)
    (h1 : (g 1 : ℂ) ∈ sphere (0 : ℂ) 1) (h01 : g 0 ≠ g 1)
    (hinterior : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
      (g t : ℂ) ∈ ball (0 : ℂ) 1) :
    let γ : unitInterval → ℂ := fun t ↦ (g t : ℂ)
    let Kopen : Set ℂ := γ '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1}
    let Ω : Set ℂ := ball (0 : ℂ) 1 \ Kopen
    ∃ x y : ℂ, x ∈ Ω ∧ y ∈ Ω ∧
      connectedComponentIn Ω x ≠ connectedComponentIn Ω y := by
  dsimp only
  by_contra hnot
  have hsame : ∀ x y : ℂ, x ∈ ball (0 : ℂ) 1 \
      (fun t : unitInterval ↦ (g t : ℂ)) ''
        {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} →
      y ∈ ball (0 : ℂ) 1 \
      (fun t : unitInterval ↦ (g t : ℂ)) ''
        {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} →
      connectedComponentIn (ball (0 : ℂ) 1 \
        (fun t : unitInterval ↦ (g t : ℂ)) ''
          {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1}) x =
      connectedComponentIn (ball (0 : ℂ) 1 \
        (fun t : unitInterval ↦ (g t : ℂ)) ''
          {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1}) y := by
    intro x y hx hy
    by_contra hxy
    exact hnot ⟨x, y, hx, hy, hxy⟩
  exact cairns_round_disk_polygon_separator g hg h0 h1 h01 hinterior hsame

end HolomorphicAnosov

