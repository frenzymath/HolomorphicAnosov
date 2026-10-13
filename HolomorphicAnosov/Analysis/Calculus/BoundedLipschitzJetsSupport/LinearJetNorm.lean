import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.LinearJetSubtypeSurjective

noncomputable section

namespace HolomorphicAnosov.BoundedLipschitzJets

open Filter Set
open scoped Topology _root_.Topology

variable (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- HPS Theorem (3.3), pp.27 and29, implicit operator-norm identification. The global operator bound gives one inequality. For each eventual slope bound, apply it to a sufficiently small positive multiple of any nonzero vector and cancel the scalar; the operator norm bound gives the reverse inequality after taking the infimum. -/
theorem linearJet_norm_eq_opNorm (L : X →L[ℝ] Y) :
    ‖linearJet X Y L‖ = ‖L‖ := by
  change representativeSlope X Y (linearRepresentative X Y L) = ‖L‖
  have hbound : ‖L‖ ∈ slopeBounds X Y (linearRepresentative X Y L : X → Y) := by
    refine ⟨norm_nonneg _, Filter.Eventually.of_forall ?_⟩
    intro x
    exact L.le_opNorm x
  have hbdd : BddBelow (slopeBounds X Y (linearRepresentative X Y L : X → Y)) :=
    ⟨0, fun _ h ↦ h.1⟩
  have hs : (slopeBounds X Y (linearRepresentative X Y L : X → Y)).Nonempty :=
    ⟨‖L‖, hbound⟩
  apply le_antisymm
  · exact csInf_le hbdd hbound
  · apply le_csInf hs
    intro C hC
    apply L.opNorm_le_bound hC.1
    intro v
    by_cases hv : v = 0
    · subst v; simp
    · rcases (mem_nhdsWithin_iff_exists_mem_nhds_inter).1 hC.2 with ⟨u, hu, hu_sub⟩
      rcases Metric.mem_nhds_iff.1 hu with ⟨δ, hδ, hball⟩
      let t : ℝ := δ / (2 * ‖v‖)
      have ht : 0 < t := by dsimp [t]; positivity
      have htvball : t • v ∈ Metric.ball (0 : X) δ := by
        rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        dsimp [t]
        field_simp
        linarith
      have htvne : t • v ≠ 0 := smul_ne_zero ht.ne' hv
      have htv := hu_sub ⟨hball htvball, htvne⟩
      change ‖L (t • v)‖ ≤ C * ‖t • v‖ at htv
      simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at htv
      apply le_of_mul_le_mul_left ?_ ht
      simpa [mul_assoc, mul_comm, mul_left_comm] using htv


end HolomorphicAnosov.BoundedLipschitzJets

