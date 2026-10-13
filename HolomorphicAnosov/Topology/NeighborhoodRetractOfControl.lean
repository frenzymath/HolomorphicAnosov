import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Restricting a controlled retraction to an open neighborhood

Source: Hatcher, *Algebraic Topology*, Theorem A.7, printed p.526, final paragraph.
Control of a map near a closed set gives continuity across that set and places it
in the interior of the map's domain.
-/

namespace HolomorphicAnosov
open Set
open scoped Topology _root_.Topology

/-- A map fixing a closed subset and continuous off it restricts to a neighborhood
retraction if it has arbitrarily small images near the subset and its domain
contains a neighborhood of each subset point.

Source: Hatcher, *Algebraic Topology*, Theorem A.7, printed p.526. At a point of
C, combine the displayed control on Z with the identity on C to prove continuity
on Z ∪ C. Outside C, closedness gives a neighborhood disjoint from C, where this
is the existing continuity on Z. Each displayed ball lies in Z ∪ C, so every
point of C lies in its interior U. Restriction to U gives the continuous map,
and the identity equation is inherited from the original map. -/
theorem neighborhood_retract_of_control
    {E : Type*} [MetricSpace E] (C Z : Set E) (hC : IsClosed C)
    (r : E → C) (hr : ContinuousOn r Z) (hfix : ∀ c : C, r c = c)
    (hcontrol : ∀ c : C, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      Metric.ball c.val δ ⊆ Z ∪ C ∧
      ∀ z ∈ Z, dist z c.val < δ → dist (r z).val c.val < ε) :
    ∃ (U : Set E) (hCU : C ⊆ U), IsOpen U ∧
      ∃ f : C(U, C), ∀ c : C, f ⟨c.val, hCU c.property⟩ = c := by
  have hcont : ContinuousOn r (Z ∪ C) := by
    intro x hx
    by_cases hxc : x ∈ C
    · apply Metric.continuousWithinAt_iff.mpr
      intro ε hε
      obtain ⟨δ, hδ, hball, hsmall⟩ := hcontrol ⟨x, hxc⟩ ε hε
      refine ⟨min δ ε, lt_min hδ hε, ?_⟩
      intro z hz hzx
      rw [hfix ⟨x, hxc⟩]
      rcases hz with hz | hz
      · exact hsmall z hz (lt_of_lt_of_le hzx (min_le_left _ _))
      · rw [hfix ⟨z, hz⟩]
        exact lt_of_lt_of_le hzx (min_le_right _ _)
    · apply (hr x (hx.resolve_right hxc)).congr_set
      filter_upwards [hC.isOpen_compl.mem_nhds hxc] with y hy
      simp only [Set.mem_compl_iff] at hy
      simp [hy]
  have hCU : C ⊆ interior (Z ∪ C) := by
    intro c hc
    obtain ⟨δ, hδ, hball, _⟩ := hcontrol ⟨c, hc⟩ 1 zero_lt_one
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (Metric.ball_mem_nhds c hδ) hball)
  refine ⟨interior (Z ∪ C), hCU, isOpen_interior, ?_⟩
  exact ⟨⟨fun x ↦ r x.val, (hcont.mono interior_subset).domRestrict⟩, hfix⟩

end HolomorphicAnosov
