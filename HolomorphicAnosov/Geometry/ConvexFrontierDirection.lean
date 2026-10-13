import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace HolomorphicAnosov
open Set

/-- The normalized direction from an interior point of a convex planar set is injective on its
frontier. (Lyubich, §2.4.4, p.66) -/
theorem convex_frontier_normalized_direction_injective
    {S : Set ℂ} (hS : Convex ℝ S) {a : ℂ} (ha : a ∈ interior S) :
    InjOn (fun z : ℂ ↦ (z - a) / (‖z - a‖ : ℂ)) (frontier S) := by
  intro x hx y hy hxy
  have hxa : x ≠ a := fun h ↦ hx.2 (h ▸ ha)
  have hya : y ≠ a := fun h ↦ hy.2 (h ▸ ha)
  have hxpos : 0 < ‖x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxa)
  have hypos : 0 < ‖y - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hya)
  have hm : (x-a) * (‖y-a‖ : ℂ) = (y-a) * (‖x-a‖ : ℂ) :=
    (div_eq_div_iff (by exact_mod_cast hxpos.ne') (by exact_mod_cast hypos.ne')).mp hxy
  have hnear {x y : ℂ} (hx : x ∈ frontier S) (hy : y ∈ frontier S)
      (hxpos : 0 < ‖x-a‖) (hypos : 0 < ‖y-a‖)
      (hm : (x-a) * (‖y-a‖ : ℂ) = (y-a) * (‖x-a‖ : ℂ)) :
      ¬ ‖x-a‖ < ‖y-a‖ := by
    intro hlt
    let r : ℝ := ‖x-a‖ / ‖y-a‖
    have hr0 : 0 < r := div_pos hxpos hypos
    have hr1 : r < 1 := (div_lt_one hypos).mpr hlt
    have halg : (1-r) • a + r • y = x := by
      simp only [Algebra.smul_def]
      dsimp [r]
      push_cast
      field_simp [show (‖y-a‖ : ℂ) ≠ 0 by exact_mod_cast hypos.ne']
      linear_combination -hm
    apply hx.2
    apply hS.openSegment_interior_closure_subset_interior ha hy.1
    rw [← halg]
    exact ⟨1-r, r, by linarith, hr0, by ring, rfl⟩
  have hn : ‖x-a‖ = ‖y-a‖ := le_antisymm
    (le_of_not_gt (hnear hy hx hypos hxpos hm.symm))
    (le_of_not_gt (hnear hx hy hxpos hypos hm))
  rw [hn] at hm
  have heq := mul_right_cancel₀ (by exact_mod_cast hypos.ne' : (‖y-a‖ : ℂ) ≠ 0) hm
  exact sub_left_injective heq
end HolomorphicAnosov
