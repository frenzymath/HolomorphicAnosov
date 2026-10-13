import HolomorphicAnosov.Topology.CairnsHalfDiskSeamPreimage
import Mathlib.Analysis.Complex.ReImTopology

open Set Metric

namespace HolomorphicAnosov.Topology

/-! Elementary interior and frontier facts for the closed half disks.

These are separated from the chart construction so that the final relative-chart
image argument can use the sign of the imaginary part without unfolding the
half-disk definition at every occurrence.
-/

theorem cairns_halfdisk_interior (upper : Bool) :
    interior (cairnsClosedHalfDisk upper) =
      ball (0 : ℂ) 1 ∩
        if upper then {z : ℂ | 0 < z.im} else {z : ℂ | z.im < 0} := by
  cases upper with
  | false =>
      simp only [cairnsClosedHalfDisk, Bool.false_eq_true, ↓reduceIte]
      rw [interior_inter, interior_closedBall]
      change ball (0 : ℂ) 1 ∩ interior (Complex.im ⁻¹' Iic (0 : ℝ)) = _
      rw [Complex.interior_preimage_im, interior_Iic]
      ext z
      rfl
      all_goals norm_num
  | true =>
      simp only [cairnsClosedHalfDisk, ↓reduceIte]
      rw [interior_inter, interior_closedBall]
      change ball (0 : ℂ) 1 ∩ interior (Complex.im ⁻¹' Ici (0 : ℝ)) = _
      rw [Complex.interior_preimage_im, interior_Ici]
      ext z
      rfl
      all_goals norm_num

theorem cairns_halfdisk_frontier_ball_im_eq_zero (upper : Bool)
    {z : ℂ} (hz : z ∈ frontier (cairnsClosedHalfDisk upper))
    (hzball : z ∈ ball (0 : ℂ) 1) : z.im = 0 := by
  cases upper with
  | false =>
      have hclosed : IsClosed (cairnsClosedHalfDisk false) := by
        simp only [cairnsClosedHalfDisk, Bool.false_eq_true, ↓reduceIte]
        exact isClosed_closedBall.inter
          (isClosed_le Complex.continuous_im continuous_const)
      rw [hclosed.frontier_eq, cairns_halfdisk_interior false] at hz
      have hzle : z.im ≤ 0 := by
        simpa only [cairnsClosedHalfDisk, Bool.false_eq_true, ↓reduceIte,
          mem_inter_iff, mem_closedBall, mem_ofPred_eq] using hz.1.2
      rcases lt_or_eq_of_le hzle with hlt | heq
      · have hn : ¬ z.im < 0 := by
          intro hneg
          exact hz.2 ⟨hzball, hneg⟩
        exact (hn hlt).elim
      · exact heq
  | true =>
      have hclosed : IsClosed (cairnsClosedHalfDisk true) := by
        simp only [cairnsClosedHalfDisk, ↓reduceIte]
        exact isClosed_closedBall.inter
          (isClosed_le continuous_const Complex.continuous_im)
      rw [hclosed.frontier_eq, cairns_halfdisk_interior true] at hz
      have hzge : 0 ≤ z.im := by
        simpa only [cairnsClosedHalfDisk, mem_inter_iff, mem_closedBall,
          mem_ofPred_eq, ite_true] using hz.1.2
      rcases lt_or_eq_of_le hzge with hlt | heq
      · have hn : ¬ 0 < z.im := by
          intro hpos
          exact hz.2 ⟨hzball, hpos⟩
        exact (hn hlt).elim
      · exact heq.symm


/-- In a half-disk chart, the preimage of the open unit disk is the cell interior
plus the prescribed diameter seam with its two endpoints removed. The interior
image formula handles the open cell; a frontier point in the open disk must lie
on the diameter, and the affine seam parametrization detects the endpoints. -/
theorem cairns_halfdisk_ball_preimage (upper : Bool) (U c B : Set ℂ) (p q : ℂ)
    (H : closure U ≃ₜ cairnsClosedHalfDisk upper)
    (hc : B ⊆ closure U) (hclosure : closure U = U ∪ c)
    (hU : H '' {z : closure U | (z : ℂ) ∈ U} =
      {w : cairnsClosedHalfDisk upper | (w : ℂ) ∈ interior (cairnsClosedHalfDisk upper)})
    (hC : H '' {z : closure U | (z : ℂ) ∈ c} =
      {w : cairnsClosedHalfDisk upper | (w : ℂ) ∈ frontier (cairnsClosedHalfDisk upper)})
    (b : unitInterval → ℂ) (hrange : range b = B) (h0 : b 0 = p) (h1 : b 1 = q)
    (hB : ∀ t : unitInterval, (H ⟨b t, hc (hrange ▸ mem_range_self t)⟩ : ℂ) =
      ((2 * (t : ℝ) - 1 : ℝ) : ℂ)) :
    ∀ z : closure U, (H z : ℂ) ∈ ball (0 : ℂ) 1 ↔ (z : ℂ) ∈ U ∪ (B \ {p, q}) := by
  intro z
  have hpre := cairns_halfdisk_seam_preimage U B H hc b hrange hB
  have hendpoint (hz : (z : ℂ) ∈ ({p, q} : Set ℂ)) : (H z : ℂ) ∉ ball (0 : ℂ) 1 := by
    simp only [mem_insert_iff, mem_singleton_iff] at hz
    rcases hz with hz | hz
    · have he : z = ⟨b 0, hc (hrange ▸ mem_range_self 0)⟩ := by
        apply Subtype.ext
        exact hz.trans h0.symm
      rw [he, hB]
      norm_num
    · have he : z = ⟨b 1, hc (hrange ▸ mem_range_self 1)⟩ := by
        apply Subtype.ext
        exact hz.trans h1.symm
      rw [he, hB]
      norm_num
  constructor
  · intro hzball
    have hzcl : (z : ℂ) ∈ U ∪ c := by simpa only [← hclosure] using z.property
    rcases hzcl with hzU | hzc
    · exact Or.inl hzU
    · have hzfront : (H z : ℂ) ∈ frontier (cairnsClosedHalfDisk upper) := by
        have hm : H z ∈ H '' {z : closure U | (z : ℂ) ∈ c} := ⟨z, hzc, rfl⟩
        rwa [hC] at hm
      have hzim := cairns_halfdisk_frontier_ball_im_eq_zero upper hzfront hzball
      exact Or.inr ⟨(hpre z).mp ⟨(H z).property.1, hzim⟩,
        fun he ↦ hendpoint he hzball⟩
  · rintro (hzU | ⟨hzB, hzne⟩)
    · have hzint : (H z : ℂ) ∈ interior (cairnsClosedHalfDisk upper) := by
        have hm : H z ∈ H '' {z : closure U | (z : ℂ) ∈ U} := ⟨z, hzU, rfl⟩
        rwa [hU] at hm
      rw [cairns_halfdisk_interior] at hzint
      exact hzint.1
    · obtain ⟨t, ht⟩ := hrange ▸ hzB
      have he : z = ⟨b t, hc (hrange ▸ mem_range_self t)⟩ := by
        apply Subtype.ext
        exact ht.symm
      have ht0 : (t : ℝ) ≠ 0 := by
        intro ht0
        have ht0' : t = 0 := Subtype.ext ht0
        apply hzne
        left
        exact ht.symm.trans (ht0' ▸ h0)
      have ht1 : (t : ℝ) ≠ 1 := by
        intro ht1
        have ht1' : t = 1 := Subtype.ext ht1
        apply hzne
        right
        exact ht.symm.trans (ht1' ▸ h1)
      rw [he, hB, mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> nlinarith [lt_of_le_of_ne t.property.1 ht0.symm,
        lt_of_le_of_ne t.property.2 ht1]

end HolomorphicAnosov.Topology
