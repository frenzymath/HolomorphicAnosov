import HolomorphicAnosov.Topology.CairnsRadialPointUniqueness

namespace HolomorphicAnosov
open Set

/-- Noncentral points in a closed radial sweep have unique front and parameter.

This is the uniqueness clause used in Cairns §4(A), pp.863--864. -/
theorem cairns_radial_sweep_unique
    {N : ℂ} {L : Set ℂ} (hN : ∀ Q ∈ L, Q ≠ N)
    {D : Type*} [TopologicalSpace D] (d : L ≃ₜ D) (dir : D → Circle)
    (hdir_inj : Function.Injective dir)
    (hd : ∀ Q : L, ((dir (d Q) : Circle) : ℂ) =
      ((Q : ℂ) - N) / (‖(Q : ℂ) - N‖ : ℂ))
    {z : ℂ} (hz : ∃ Q ∈ L, ∃ t ∈ Icc (0 : ℝ) 1,
      z = (1 - t) • N + t • Q)
    (hzN : z ≠ N) :
    ∃! w : L × Icc (0 : ℝ) 1,
      z = (1 - (w.2 : ℝ)) • N + (w.2 : ℝ) • (w.1 : ℂ) := by
  rcases hz with ⟨Q, hQL, t, ht, hzt⟩
  have ht0 : (t : ℝ) ≠ 0 := by
    intro ht0
    apply hzN
    rw [hzt, ht0]
    simp
  have htpos : 0 < (t : ℝ) := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hzt' : z = (1 - t) • N + t • ((⟨Q, hQL⟩ : L) : ℂ) := by simpa using hzt
  refine ⟨(⟨Q, hQL⟩, ⟨t, ht⟩), hzt', ?_⟩
  intro w hw
  rcases w with ⟨R, u⟩
  have hu0 : (u : ℝ) ≠ 0 := by
    intro hu0
    apply hzN
    rw [hw, hu0]
    simp
  have hupos : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (Ne.symm hu0)
  have hw' : z = (1 - (u : ℝ)) • N + (u : ℝ) • (R : ℂ) := by simpa using hw
  have hQRt := cairns_radial_point_unique (Q := (⟨Q, hQL⟩ : L)) (R := R)
    (t := t) (u := (u : ℝ)) hN d dir hdir_inj hd htpos hupos
    (hzt'.symm.trans hw')
  exact Prod.ext hQRt.1.symm (Subtype.ext hQRt.2.symm)

end HolomorphicAnosov
