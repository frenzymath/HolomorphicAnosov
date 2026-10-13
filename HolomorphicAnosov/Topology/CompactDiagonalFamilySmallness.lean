import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.ContinuousOn
import Mathlib.Order.Filter.AtTopBot.Basic

open Set Filter Metric
open scoped Topology

namespace HolomorphicAnosov

/-- A relatively continuous family vanishing on the compact diagonal is uniformly
small in a compact parameter when its two base entries approach one another.
The relation D need not be open. Relative continuity gives an ambient open
neighborhood of diagonal(X) times T on which F is small in D times T; compactness
gives a uniform positive thickening. A pair with nearby entries is close to its
own diagonal pair at every parameter, which proves the assertion.

Source: agent-written compact-family shrinking step for Zhang, Lemma 2.7,
printed p.9, equation (18). The parameter will be the radial interval in a
local stable-coordinate target ball. -/
theorem compact_diagonal_family_eventually_small
    {X T : Type*} [MetricSpace X] [CompactSpace X]
    [MetricSpace T] [CompactSpace T]
    (D : Set (X × X)) (F : (X × X) × T → ℝ)
    (hF : ContinuousOn F (D ×ˢ Set.univ))
    (hdiag : ∀ x, (x, x) ∈ D) (hzero : ∀ x t, F ((x, x), t) = 0)
    (x y : ℕ → X) (hD : ∀ᶠ n in atTop, (x n, y n) ∈ D)
    (hclose : Tendsto (fun n ↦ dist (x n) (y n)) atTop (𝓝 (0 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t, F ((x n, y n), t) < ε := by
  obtain ⟨N, hN, hND⟩ := (_root_.continuousOn_iff'.mp hF) (Iio ε) isOpen_Iio
  have hdiagN : diagonal X ×ˢ (Set.univ : Set T) ⊆ N := by
    rintro ⟨⟨a, b⟩, t⟩ ⟨hab, _⟩
    have heq : a = b := hab
    subst b
    have hm : ((a, a), t) ∈ F ⁻¹' Iio ε ∩ (D ×ˢ Set.univ) :=
      ⟨by simpa only [Set.mem_preimage, Set.mem_Iio, hzero] using hε,
        hdiag a, Set.mem_univ t⟩
    rw [hND] at hm
    exact hm.1
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_diagonal.prod isCompact_univ).exists_thickening_subset_open
    hN hdiagN
  filter_upwards [hD, hclose.eventually (gt_mem_nhds hδ)] with n hn hdist
  intro t
  have hmN : ((x n, y n), t) ∈ N := hthick (mem_thickening_iff.mpr
    ⟨((x n, x n), t), ⟨rfl, Set.mem_univ t⟩,
      by simpa only [dist_prod_same_right, dist_prod_same_left, dist_comm] using hdist⟩)
  have hm : ((x n, y n), t) ∈ N ∩ (D ×ˢ Set.univ) :=
    ⟨hmN, hn, Set.mem_univ t⟩
  rw [← hND] at hm
  exact hm.1

end HolomorphicAnosov

