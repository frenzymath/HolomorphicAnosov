import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Visible
import Mathlib.Analysis.Normed.Module.Ray

open Set

namespace HolomorphicAnosov

private theorem radial_eq_of_wbtw {M x y : ℂ} (h : Wbtw ℝ M x y)
    (hx : x ≠ M) (hy : y ≠ M) :
    (x-M) / (‖x-M‖ : ℂ) = (y-M) / (‖y-M‖ : ℂ) := by
  have hs : SameRay ℝ (x-M) (y-M) := h.sameRay_vsub_left
  have heq := hs.inv_norm_smul_eq (sub_ne_zero.mpr hx) (sub_ne_zero.mpr hy)
  simpa [Algebra.smul_def, div_eq_mul_inv, mul_comm] using heq

/-- The visible part of a closed hull between an apex and an opposite base
has exactly the directions of that base.

Source: agent-written ray-intersection expansion of Cairns (1951), §3 Case II
p.863 and §4(A), pp.863–864. Every triangle point lies on an apex-to-base
segment. Conversely, the first intersection of a ray through a base point
with the closed hull is visible. The apex lies outside the hull, so none of
these intersections is zero and normalization preserves the ray direction.
Convexity of the hull is unnecessary for this image statement. -/
theorem halfSector_visible_radial_image
    (M D P : ℂ) (K : Set ℂ) (hK : IsClosed K) (hM : M ∉ K)
    (hbase : segment ℝ D P ⊆ K) (htriangle : K ⊆ convexHull ℝ {M, P, D}) :
    (fun Q : ℂ ↦ (Q-M) / (‖Q-M‖ : ℂ)) '' {Q | Q ∈ K ∧ IsVisible ℝ K M Q} =
      (fun Q : ℂ ↦ (Q-M) / (‖Q-M‖ : ℂ)) '' segment ℝ D P := by
  apply Subset.antisymm
  · rintro z ⟨x, ⟨hx, hv⟩, rfl⟩
    have hxtri := htriangle hx
    rw [convexHull_insert (insert_nonempty P {D}), convexHull_pair,
      mem_convexJoin] at hxtri
    obtain ⟨a, ha, y, hy, hxy⟩ := hxtri
    have haM : a = M := mem_singleton_iff.mp ha
    subst a
    have hybase : y ∈ segment ℝ D P := by simpa [segment_symm] using hy
    refine ⟨y, hybase, ?_⟩
    exact (radial_eq_of_wbtw (mem_segment_iff_wbtw.mp hxy)
      (ne_of_mem_of_not_mem hx hM) (ne_of_mem_of_not_mem (hbase hybase) hM)).symm
  · rintro z ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy, hv⟩ := hK.exists_wbtw_isVisible (hbase hy) M
    exact ⟨x, ⟨hx, hv⟩, radial_eq_of_wbtw hxy
      (ne_of_mem_of_not_mem hx hM) (ne_of_mem_of_not_mem (hbase hy) hM)⟩

end HolomorphicAnosov

