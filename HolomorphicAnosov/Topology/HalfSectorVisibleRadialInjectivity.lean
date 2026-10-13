import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Visible

/-!
# Radial injectivity on a visible front

Agent-written ray-order argument for Cairns (1951), §3 Case II and §4(A),
pp.862–864. Visibility alone rules out two distinct front points on one positive
ray. Convexity and compactness are not needed for this uniqueness assertion.
-/
namespace HolomorphicAnosov
open Set

private theorem visible_direction_eq_of_norm_le
    (M x y : ℂ) (K : Set ℂ) (hM : M ∉ K) (hx : x ∈ K) (hy : y ∈ K)
    (hvy : IsVisible ℝ K M y) (hle : ‖x - M‖ ≤ ‖y - M‖)
    (heq : (x - M) / (‖x - M‖ : ℂ) = (y - M) / (‖y - M‖ : ℂ)) : x = y := by
  have hxM : x ≠ M := ne_of_mem_of_not_mem hx hM
  have hyM : y ≠ M := ne_of_mem_of_not_mem hy hM
  have hnx : 0 < ‖x - M‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxM)
  have hny : 0 < ‖y - M‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyM)
  have hnxC : (‖x - M‖ : ℂ) ≠ 0 := by exact_mod_cast hnx.ne'
  have hnyC : (‖y - M‖ : ℂ) ≠ 0 := by exact_mod_cast hny.ne'
  have hmul := (div_eq_div_iff hnxC hnyC).mp heq
  let k : ℝ := ‖x - M‖ / ‖y - M‖
  have hk0 : 0 < k := div_pos hnx hny
  have hk1 : k ≤ 1 := (div_le_one hny).mpr hle
  have hratio : x - M = (k : ℂ) * (y - M) := by
    dsimp [k]
    calc
      x - M = ((x - M) * (‖y - M‖ : ℂ)) / (‖y - M‖ : ℂ) := by field_simp
      _ = ((y - M) * (‖x - M‖ : ℂ)) / (‖y - M‖ : ℂ) := by rw [hmul]
      _ = ((‖x - M‖ / ‖y - M‖ : ℝ) : ℂ) * (y - M) := by
        rw [Complex.ofReal_div]
        ring
  have hcomb : AffineMap.lineMap M y k = x := by
    rw [AffineMap.lineMap_apply_module]
    simp only [Algebra.smul_def]
    push_cast
    linear_combination -hratio
  rcases eq_or_lt_of_le hk1 with hk | hk
  · simpa [hk] using hcomb.symm
  · exact False.elim (((isVisible_iff_lineMap hyM.symm).mp hvy) k ⟨hk0, hk⟩
      (hcomb.symm ▸ hx))

/-- The normalized direction map is injective on the points of `K` visible
from an exterior apex `M`.

Proof: order two points by distance from `M`. Equal normalized directions
express the closer point as the affine radial combination with parameter equal
to the ratio of distances. The ratio is positive and at most one. If it is less
than one, this point of `K` blocks visibility of the farther point. Thus the ratio
is one and the two points are equal. Exchange the two points for the opposite
ordering. -/
theorem halfSector_visible_radial_injOn
    (M : ℂ) (K : Set ℂ) (hM : M ∉ K) :
    Set.InjOn (fun Q : ℂ ↦ (Q - M) / (‖Q - M‖ : ℂ))
      {Q | Q ∈ K ∧ IsVisible ℝ K M Q} := by
  intro x hx y hy heq
  rcases le_total ‖x - M‖ ‖y - M‖ with hle | hle
  · exact visible_direction_eq_of_norm_le M x y K hM hx.1 hy.1 hy.2 hle heq
  · exact (visible_direction_eq_of_norm_le M y x K hM hy.1 hx.1 hx.2 hle heq.symm).symm

end HolomorphicAnosov
