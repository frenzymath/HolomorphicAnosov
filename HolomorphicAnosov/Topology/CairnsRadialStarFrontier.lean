import HolomorphicAnosov.Topology.CairnsRadialStarOpen
import HolomorphicAnosov.Topology.CairnsRadialStarClosure
import HolomorphicAnosov.Topology.CairnsFrontBaseEndpoints
import HolomorphicAnosov.Topology.CairnsBaseSegmentInSweep

namespace HolomorphicAnosov
open Set

/-- The frontier of the strict Cairns radial star is its front together with its base.

Source: Cairns (1951), §4(A), printed pp.863–864. The star is open and its
closure is the closed sweep. A sweep point omitted by the star is either the
center, a front point, or on a boundary direction. The front's two boundary
directions have precisely the specified base endpoints, so those two rays form
the base segment. Conversely, the base has zero transverse coordinate, while
radial uniqueness excludes front points from the strict star. -/
theorem cairns_radial_star_frontier
    (E₁ E₂ Eₚ : ℂ) (ν : Set ℂ) (hν : IsCompact ν)
    (hE : E₁ ≠ E₂)
    (hSide : (star (E₂ - E₁) * (Eₚ - E₁)).im ≠ 0)
    (hE₁ : E₁ ∈ ν) (hE₂ : E₂ ∈ ν)
    (hN : (E₁ + E₂) / 2 ∉ ν)
    (ds : ν ≃ₜ {v : Circle | 0 ≤
      (star (E₂ - E₁) * (Eₚ - E₁)).im * (star (E₂ - E₁) * (v : ℂ)).im})
    (hds : ∀ Q : ν, ((ds Q : Circle) : ℂ) =
      ((Q : ℂ) - (E₁ + E₂) / 2) / (‖(Q : ℂ) - (E₁ + E₂) / 2‖ : ℂ)) :
    let N := (E₁ + E₂) / 2
    frontier {z : ℂ | ∃ Q ∈ ν, ∃ t ∈ Ioo (0 : ℝ) 1,
      z = (1 - t) • N + t • Q ∧
      0 < (star (E₂ - E₁) * (Eₚ - E₁)).im * (star (E₂ - E₁) * (z - E₁)).im} =
      segment ℝ E₁ E₂ ∪ ν := by
  dsimp only
  let N := (E₁ + E₂) / 2
  let c := (star (E₂ - E₁) * (Eₚ - E₁)).im
  let d := E₂ - E₁
  let γ := {z : ℂ | ∃ Q ∈ ν, ∃ t ∈ Ioo (0 : ℝ) 1,
    z = (1 - t) • N + t • Q ∧ 0 < c * (star d * (z - E₁)).im}
  let S := {z : ℂ | ∃ Q ∈ ν, ∃ t ∈ Icc (0 : ℝ) 1,
    z = (1 - t) • N + t • Q}
  let A := {v : Circle | 0 ≤ c * (star d * (v : ℂ)).im}
  have hopen : IsOpen γ := cairns_radial_star_isOpen E₁ E₂ Eₚ ν hν hE hSide hE₁ hE₂ hN ds hds
  have hcl : closure γ = S := cairns_radial_star_closure_eq_sweep E₁ E₂ Eₚ ν hν hE hSide hN ds hds
  change frontier γ = _
  rw [hopen.frontier_eq, hcl]
  have hN' : N ∉ ν := hN
  have hNall : ∀ Q ∈ ν, Q ≠ N := by
    intro Q hQ heq
    exact hN' (heq ▸ hQ)
  have hNseg : N ∈ segment ℝ E₁ E₂ := by
    rw [segment_eq_image ℝ E₁ E₂]
    refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    dsimp [N]
    push_cast
    ring
  have hcross (z : ℂ) : (star d * (z - E₁)).im = (star d * (z - N)).im := by
    simp [d, N, Complex.mul_im]
    ring
  have hsideQ (Q : ν) : 0 ≤ c * (star d * ((Q : ℂ) - E₁)).im := by
    have h := (ds Q).property
    change 0 ≤ c * (star d * ((ds Q : Circle) : ℂ)).im at h
    rw [hds, ← mul_div_assoc, Complex.div_ofReal_im, ← mul_div_assoc] at h
    have hn : 0 < ‖(Q : ℂ) - N‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hNall Q Q.property))
    rw [hcross]
    have hmul := (le_div_iff₀ hn).mp h
    simpa only [zero_mul] using hmul
  have hcrossRay (Q : ℂ) (t : ℝ) :
      (star d * ((1 - t) • N + t • Q - E₁)).im =
        t * (star d * (Q - E₁)).im := by
    simp [d, N, Complex.mul_im, Complex.real_smul]
    ring
  ext z
  constructor
  · rintro ⟨⟨Q, hQ, t, ht, heq⟩, hznot⟩
    by_cases htzero : t = 0
    · left
      rw [heq, htzero]
      simpa using hNseg
    by_cases htone : t = 1
    · right
      rw [heq, htone]
      simpa using hQ
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
    have htlt : t < 1 := lt_of_le_of_ne ht.2 htone
    have hnotside : ¬ 0 < c * (star d * (z - E₁)).im := by
      intro hs
      exact hznot ⟨Q, hQ, t, ⟨htpos, htlt⟩, heq, hs⟩
    have hzside : c * (star d * (z - E₁)).im =
        t * (c * (star d * (Q - E₁)).im) := by
      rw [heq, hcrossRay]
      ring
    have hzero : c * (star d * (Q - E₁)).im = 0 := by
      rw [hzside] at hnotside
      nlinarith [hsideQ ⟨Q, hQ⟩]
    have hbase : (star d * (Q - E₁)).im = 0 := (mul_eq_zero.mp hzero).resolve_left hSide
    left
    rcases cairns_front_base_endpoints E₁ E₂ Eₚ ν hE hE₁ hE₂ hN ds hds hQ hbase with h | h
    · rw [heq, h]
      exact (convex_segment E₁ E₂) hNseg (left_mem_segment ℝ E₁ E₂)
        (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    · rw [heq, h]
      exact (convex_segment E₁ E₂) hNseg (right_mem_segment ℝ E₁ E₂)
        (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  · intro hz
    rcases hz with hz | hz
    · refine ⟨cairns_base_segment_subset_sweep E₁ E₂ ν hE₁ hE₂ hz, ?_⟩
      rintro ⟨Q, hQ, t, ht, heq, hside⟩
      have hbase : (star d * (z - E₁)).im = 0 := by
        obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
        have ha' : a = 1 - b := by linarith
        rw [ha']
        simp [d, Complex.mul_im, Complex.real_smul]
        ring
      rw [hbase, mul_zero] at hside
      exact lt_irrefl 0 hside
    · refine ⟨⟨z, hz, 1, by norm_num, by simp⟩, ?_⟩
      rintro ⟨Q, hQ, t, ht, heq, hside⟩
      have heq' : (1 - t) • N + t • Q = (1 - (1 : ℝ)) • N + (1 : ℝ) • z := by
        simpa using heq.symm
      have hu := cairns_radial_point_unique hNall ds (fun v : A ↦ (v : Circle))
        Subtype.val_injective hds (Q := ⟨Q, hQ⟩) (R := ⟨z, hz⟩) ht.1 zero_lt_one heq'
      exact (ne_of_lt ht.2) hu.2

end HolomorphicAnosov
