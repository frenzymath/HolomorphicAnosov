import HolomorphicAnosov.Topology.PolygonEdgeLocalLine
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Convex

/-! Local half-disks at an interior chord point. Source: Cairns (1951),
Lemma 3.1, pp.861–862. Only affine and convex geometry is used here. -/

open Set Metric
namespace HolomorphicAnosov

/-- Every interior point of a nondegenerate complex segment in an open set has
a ball contained in that set whose complement of the open segment consists
of its positive and negative oriented half-disks. Both half-disks are nonempty
and connected. Source: Cairns (1951), Lemma 3.1, pp.861–862, local straight-edge
geometry. Use the existing local-line theorem and avoid the two endpoints.
The oriented area is an open affine real functional, so each ball centered
on its zero line meets both signs. Each sign intersection is convex. -/
theorem chord_local_half_disks {a b z : ℂ} (hab : a ≠ b)
    (hz : z ∈ openSegment ℝ a b) {U : Set ℂ} (hU : IsOpen U) (hzU : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball z r ⊆ U ∧
      let P := {w ∈ ball z r | 0 < (star (b - a) * (w - a)).im}
      let N := {w ∈ ball z r | (star (b - a) * (w - a)).im < 0}
      P.Nonempty ∧ N.Nonempty ∧ IsConnected P ∧ IsConnected N ∧
        ball z r \ openSegment ℝ a b = P ∪ N := by
  obtain ⟨s, hs, hline⟩ := segment_local_line hab hz
  have hza : z ≠ a := fun h ↦ hab (left_mem_openSegment_iff.mp (h ▸ hz))
  have hzb : z ≠ b := fun h ↦ hab (right_mem_openSegment_iff.mp (h ▸ hz))
  have hgood : U ∩ {a, b}ᶜ ∈ nhds z :=
    (hU.inter (isClosed_singleton.union (isClosed_singleton (x := b))).isOpen_compl).mem_nhds
      ⟨hzU, by simp [hza, hzb]⟩
  obtain ⟨t, ht, htgood⟩ := Metric.mem_nhds_iff.mp hgood
  let r := min s t
  have hr : 0 < r := lt_min hs ht
  have hrline (w : ℂ) (hw : w ∈ ball z r) :
      w ∈ openSegment ℝ a b ↔ (star (b - a) * (w - a)).im = 0 := by
    have hends := (htgood (ball_subset_ball (min_le_right s t) hw)).2
    have hwa : a ≠ w := by intro h; exact hends (by simp [h])
    have hwb : b ≠ w := by intro h; exact hends (by simp [h])
    exact ⟨fun h ↦ (hline w (ball_subset_ball (min_le_left s t) hw)).mp
      (openSegment_subset_segment ℝ a b h),
      fun h ↦ mem_openSegment_of_ne_left_right hwa hwb
        ((hline w (ball_subset_ball (min_le_left s t) hw)).mpr h)⟩
  let F : ℂ → ℝ := fun w ↦ (star (b - a) * (w - a)).im
  have hFz : F z = 0 := (hrline z (mem_ball_self hr)).mp hz
  have hv : star (b - a) ≠ 0 := star_ne_zero.mpr (sub_ne_zero.mpr hab.symm)
  have hFopen : IsOpenMap F := by
    exact Complex.isOpenMap_im.comp
      ((Homeomorph.mulLeft₀ (star (b - a)) hv).isOpenMap.comp
        (Homeomorph.addRight (-a)).isOpenMap)
  have himage : F '' ball z r ∈ nhds (0 : ℝ) := by
    apply (hFopen _ isOpen_ball).mem_nhds
    exact ⟨z, mem_ball_self hr, hFz⟩
  obtain ⟨d, hd, hdball⟩ := Metric.mem_nhds_iff.mp himage
  have hp : (d / 2) ∈ F '' ball z r := hdball (by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith)
  have hn : (-d / 2) ∈ F '' ball z r := hdball (by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_neg (by linarith)]
    linarith)
  obtain ⟨p, hpball, hpF⟩ := hp
  obtain ⟨q, hqball, hqF⟩ := hn
  let P := {w ∈ ball z r | 0 < F w}
  let N := {w ∈ ball z r | F w < 0}
  have hP : P.Nonempty := ⟨p, hpball, hpF ▸ (by positivity)⟩
  have hN : N.Nonempty := ⟨q, hqball, hqF ▸ (by linarith)⟩
  let L : ℂ →ₗ[ℝ] ℝ :=
    Complex.imLm.comp (LinearMap.mulLeft ℝ (star (b - a)))
  have hF (w : ℂ) : F w = L w - L a := by
    simp only [F, L, LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_sub, Complex.sub_im]
    rfl
  have hPc : Convex ℝ P := by
    have heq : P = ball z r ∩ {w | L a < L w} := by
      ext w; simp [P, hF, sub_pos]
    rw [heq]
    exact (convex_ball z r).inter (convex_halfSpace_gt L.isLinear (L a))
  have hNc : Convex ℝ N := by
    have heq : N = ball z r ∩ {w | L w < L a} := by
      ext w; simp [N, hF, sub_neg]
    rw [heq]
    exact (convex_ball z r).inter (convex_halfSpace_lt L.isLinear (L a))
  refine ⟨r, hr, fun w hw ↦ (htgood (ball_subset_ball (min_le_right s t) hw)).1,
    hP, hN, hPc.isConnected hP, hNc.isConnected hN, ?_⟩
  ext w
  constructor
  · rintro ⟨hw, hn⟩
    have hne : F w ≠ 0 := fun h ↦ hn ((hrline w hw).mpr h)
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact Or.inr ⟨hw, hneg⟩
    · exact Or.inl ⟨hw, hpos⟩
  · rintro (⟨hw, hp⟩ | ⟨hw, hn⟩)
    · exact ⟨hw, fun h ↦ hp.ne' ((hrline w hw).mp h)⟩
    · exact ⟨hw, fun h ↦ hn.ne ((hrline w hw).mp h)⟩

end HolomorphicAnosov
