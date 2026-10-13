import HolomorphicAnosov.Topology.CairnsExtremeContactSegmentCoordinates
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Complex.Circle
import Mathlib.Tactic

open Set

namespace HolomorphicAnosov

/--
A segment leaving an upper ordinate contact strictly upward can return to the
closed lower half-plane only at its contact tip.  This is the elementary edge
calculation used for the two top notch edges in Cairns's construction.
-/
theorem cairns_upper_contact_segment_tip
    (P Q z : ℂ) (hPQ : P.im < Q.im) (hz : z ∈ segment ℝ P Q)
    (hzle : z.im ≤ P.im) : z = P := by
  rw [segment_eq_image_lineMap ℝ P Q] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have ht0 : t = 0 := by
    have hti : 0 ≤ t := ht.1
    have him : (AffineMap.lineMap P Q t).im = t * (Q.im - P.im) + P.im := by
      simp [AffineMap.lineMap_apply, vsub_eq_sub, add_comm]
    rw [him] at hzle
    by_contra ht0
    have htpos : 0 < t := lt_of_le_of_ne hti (Ne.symm ht0)
    have hdiff : 0 < Q.im - P.im := sub_pos.mpr hPQ
    nlinarith
  simp [ht0, AffineMap.lineMap_apply]

/-- The lower-ordinate analogue of `cairns_upper_contact_segment_tip`. -/
theorem cairns_lower_contact_segment_tip
    (P Q z : ℂ) (hPQ : Q.im < P.im) (hz : z ∈ segment ℝ P Q)
    (hzge : P.im ≤ z.im) : z = P := by
  rw [segment_eq_image_lineMap ℝ P Q] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have ht0 : t = 0 := by
    have hti : 0 ≤ t := ht.1
    have him : (AffineMap.lineMap P Q t).im = t * (Q.im - P.im) + P.im := by
      simp [AffineMap.lineMap_apply, vsub_eq_sub, add_comm]
    rw [him] at hzge
    by_contra ht0
    have htpos : 0 < t := lt_of_le_of_ne hti (Ne.symm ht0)
    have hdiff : Q.im - P.im < 0 := sub_neg.mpr hPQ
    nlinarith
  simp [ht0, AffineMap.lineMap_apply]

end HolomorphicAnosov

namespace HolomorphicAnosov

/-- An upper notch edge meets the embedded circle only at its upper contact tip. -/
theorem cairns_upper_notch_edge_contact
    (γ : Circle → ℂ) (P Q : ℂ) (hP : P ∈ Set.range γ)
    (hmax : ∀ z ∈ Set.range γ, z.im ≤ P.im) (hPQ : P.im < Q.im) :
    segment ℝ P Q ∩ Set.range γ = {P} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨⟨left_mem_segment ℝ P Q, hP⟩, ?_⟩
  intro z hz
  exact cairns_upper_contact_segment_tip P Q z hPQ hz.1 (hmax z hz.2)

/-- A lower notch edge meets the embedded circle only at its lower contact tip. -/
theorem cairns_lower_notch_edge_contact
    (γ : Circle → ℂ) (P Q : ℂ) (hP : P ∈ Set.range γ)
    (hmin : ∀ z ∈ Set.range γ, P.im ≤ z.im) (hPQ : Q.im < P.im) :
    segment ℝ P Q ∩ Set.range γ = {P} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨⟨left_mem_segment ℝ P Q, hP⟩, ?_⟩
  intro z hz
  exact cairns_lower_contact_segment_tip P Q z hPQ hz.1 (hmin z hz.2)

end HolomorphicAnosov

namespace HolomorphicAnosov

/-- A horizontal segment above the strict ordinate bound misses the embedded curve. -/
theorem cairns_upper_rectangle_edge_disjoint
    (γ : Circle → ℂ) (A B : ℂ) (y : ℝ)
    (hA : A.im = y) (hB : B.im = y)
    (hbound : ∀ z ∈ Set.range γ, z.im < y) :
    segment ℝ A B ∩ Set.range γ = ∅ := by
  ext z
  constructor
  · intro hz
    obtain ⟨t, ht, hzt⟩ := by
      rw [segment_eq_image_lineMap ℝ A B] at hz
      exact hz.1
    have hzim : z.im = y := cairns_segment_im_eq_of_endpoints A B z y hz.1 hA hB
    exact (lt_irrefl y) (hzim ▸ hbound z hz.2)
  · intro hz
    simp at hz

/-- A horizontal segment below the strict ordinate bound misses the embedded curve. -/
theorem cairns_lower_rectangle_edge_disjoint
    (γ : Circle → ℂ) (A B : ℂ) (y : ℝ)
    (hA : A.im = y) (hB : B.im = y)
    (hbound : ∀ z ∈ Set.range γ, y < z.im) :
    segment ℝ A B ∩ Set.range γ = ∅ := by
  ext z
  constructor
  · intro hz
    obtain ⟨t, ht, hzt⟩ := by
      rw [segment_eq_image_lineMap ℝ A B] at hz
      exact hz.1
    have hzim : z.im = y := cairns_segment_im_eq_of_endpoints A B z y hz.1 hA hB
    exact (lt_irrefl y) (hzim ▸ hbound z hz.2)
  · intro hz
    simp at hz

/-- A vertical segment left of the strict real bound misses the embedded curve. -/
theorem cairns_left_rectangle_edge_disjoint
    (γ : Circle → ℂ) (A B : ℂ) (x : ℝ)
    (hA : A.re = x) (hB : B.re = x)
    (hbound : ∀ z ∈ Set.range γ, x < z.re) :
    segment ℝ A B ∩ Set.range γ = ∅ := by
  ext z
  constructor
  · intro hz
    obtain ⟨t, ht, hzt⟩ := by
      rw [segment_eq_image_lineMap ℝ A B] at hz
      exact hz.1
    have hzre : z.re = x := cairns_segment_re_eq_of_endpoints A B z x hz.1 hA hB
    exact (lt_irrefl x) (hzre ▸ hbound z hz.2)
  · intro hz
    simp at hz

/-- A vertical segment right of the strict real bound misses the embedded curve. -/
theorem cairns_right_rectangle_edge_disjoint
    (γ : Circle → ℂ) (A B : ℂ) (x : ℝ)
    (hA : A.re = x) (hB : B.re = x)
    (hbound : ∀ z ∈ Set.range γ, z.re < x) :
    segment ℝ A B ∩ Set.range γ = ∅ := by
  ext z
  constructor
  · intro hz
    obtain ⟨t, ht, hzt⟩ := by
      rw [segment_eq_image_lineMap ℝ A B] at hz
      exact hz.1
    have hzre : z.re = x := cairns_segment_re_eq_of_endpoints A B z x hz.1 hA hB
    exact (lt_irrefl x) (hzre ▸ hbound z hz.2)
  · intro hz
    simp at hz

end HolomorphicAnosov
