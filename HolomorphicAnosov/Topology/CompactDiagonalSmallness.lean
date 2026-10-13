import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.ContinuousOn
import Mathlib.Order.Filter.AtTopBot.Basic

open Set Filter Metric
open scoped Topology _root_.Topology
namespace HolomorphicAnosov

/-- A relatively continuous scalar function vanishing on the compact diagonal is eventually
small on domain pairs approaching that diagonal.

Agent-written expansion of the compact-family shrinking step in Zhang, Lemma 2.7, p.9,
equation (18). No openness of D is assumed. Relative continuity supplies an ambient open
neighborhood of the diagonal on which the function is less than epsilon within D. Compactness
of the diagonal gives a positive metric thickening contained in that neighborhood. Eventually
the pair belongs to D and its two entries are closer than that thickening radius. -/
theorem centered_coordinate_eventually_small
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (D : Set (X × X)) (F : X × X → ℝ) (hF : ContinuousOn F D)
    (hdiag : ∀ x, (x, x) ∈ D) (hzero : ∀ x, F (x, x) = 0)
    (x y : ℕ → X) (hD : ∀ᶠ n in atTop, (x n, y n) ∈ D)
    (hclose : Tendsto (fun n ↦ dist (x n) (y n)) atTop (𝓝 (0 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, F (x n, y n) < ε := by
  have hsmall_uniform :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y, (x, y) ∈ D → dist x y < δ → F (x, y) < ε := by
  
    obtain ⟨N, hN, hND⟩ := (_root_.continuousOn_iff'.mp hF) (Iio ε) isOpen_Iio
    have hdiagN : diagonal X ⊆ N := by
      rintro ⟨x, y⟩ hxy
      have heq : x = y := hxy
      subst y
      have hm : (x, x) ∈ F ⁻¹' Iio ε ∩ D := ⟨by simpa [hzero] using hε, hdiag x⟩
      rw [hND] at hm
      exact hm.1
    obtain ⟨δ, hδ, hthick⟩ := isCompact_diagonal.exists_thickening_subset_open hN hdiagN
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy hdist
    have hmN : (x, y) ∈ N := hthick (mem_thickening_iff.mpr
      ⟨(x, x), rfl, by simpa only [dist_prod_same_left, dist_comm] using hdist⟩)
    have hm : (x, y) ∈ N ∩ D := ⟨hmN, hxy⟩
    rw [← hND] at hm
    exact hm.1
  
  obtain ⟨δ, hδ, hsmall⟩ := hsmall_uniform
  filter_upwards [hD, hclose.eventually (gt_mem_nhds hδ)] with n hn hdist
  exact hsmall _ _ hn hdist


end HolomorphicAnosov
