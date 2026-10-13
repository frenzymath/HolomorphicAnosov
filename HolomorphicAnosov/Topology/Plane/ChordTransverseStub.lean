import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Topology

/-! DAG node: `topo.chord_transverse_stub_g10`. -/

open Set Metric
namespace HolomorphicAnosov

/-- Reflect a positive point in a small ball across its center on the chord.
The resulting transverse stub stays in the ball and meets the chord only at its
center. This is the local marked-stub construction in Cairns (1951), Lemma 3.1.
The affine scalar coordinate has opposite nonzero values at the reflected points;
on their segment it vanishes only at the midpoint, whereas it vanishes on the chord. -/
theorem chord_transverse_stub
    (L : ℂ →ₗ[ℝ] ℝ) {a b m x : ℂ} {r : ℝ}
    (hm : m ∈ openSegment ℝ a b) (hLm : L m = L a) (hLb : L b = L a)
    (hx : x ∈ ball m r) (hLx : L a < L x) :
    ∃ xm xp : ℂ,
      xm ∈ ball m r ∧ xp ∈ ball m r ∧ L xm < L a ∧ L a < L xp ∧
      xm ≠ xp ∧ segment ℝ xm xp ∩ segment ℝ a b = {m} ∧
      m ∈ openSegment ℝ xm xp ∧
      (¬ ∃ t : ℝ, xp - xm = t • (b-a)) := by
  let v := x-m
  have hLv : 0 < L v := by dsimp [v]; rw [map_sub, hLm]; exact sub_pos.mpr hLx
  have hplus : m+v = x := by dsimp [v]; abel
  have hminus : m-v ∈ ball m r := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
    simpa only [mem_ball, dist_eq_norm, v] using hx
  have hneq : m-v ≠ m+v := by
    intro heq
    have := congrArg L heq
    simp only [map_sub, map_add] at this
    linarith
  refine ⟨m-v, m+v, hminus, hplus.symm ▸ hx, ?_, ?_, hneq, ?_,
    mem_openSegment_sub_add m v, ?_⟩
  · simp only [map_sub, hLm]; linarith
  · simp only [map_add, hLm]; linarith
  · apply subset_antisymm
    · rintro z ⟨hzs, hzd⟩
      obtain ⟨t, ht, hzt⟩ := (segment_eq_image_lineMap ℝ (m-v) (m+v) ▸ hzs)
      obtain ⟨s, hs, hzs⟩ := (segment_eq_image_lineMap ℝ a b ▸ hzd)
      have hLz : L z = L a := by
        rw [← hzs, AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, hLb,
          sub_self, smul_zero, zero_add]
      have hcoeff : (2*t-1) * L v = 0 := by
        have := congrArg L hzt
        simp only [AffineMap.lineMap_apply_module', map_add, map_sub, map_smul,
          smul_eq_mul, hLm, hLz] at this
        nlinarith
      have htval : t = 1/2 := by
        have := (mul_eq_zero.mp hcoeff).resolve_right (ne_of_gt hLv)
        linarith
      rw [← hzt, htval]
      convert midpoint_sub_add (R := ℝ) m v using 1; simp [midpoint, one_div]
    · intro z hz
      have heq : z = m := hz
      subst z
      exact ⟨openSegment_subset_segment ℝ _ _ (mem_openSegment_sub_add m v),
        openSegment_subset_segment ℝ _ _ hm⟩
  · rintro ⟨t, ht⟩
    have := congrArg L ht
    simp only [map_sub, map_add, map_smul, hLb, sub_self, smul_zero] at this
    linarith

end HolomorphicAnosov

