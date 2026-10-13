import HolomorphicAnosov.Topology.CairnsExtremeContactAxisIndependence
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Complex.Circle
import Mathlib.Tactic

open Set

namespace HolomorphicAnosov

/-- Two noncollinear notch edges issuing from the same contact meet only there. -/
theorem cairns_notch_edges_meet_at_tip
    (P Q₁ Q₂ : ℂ) (hlin : LinearIndependent ℝ ![Q₁ - P, Q₂ - P]) :
    segment ℝ P Q₁ ∩ segment ℝ P Q₂ = {P} := by
  exact segment_inter_eq_endpoint_of_linearIndependent_sub ℝ hlin

/-- A strict upper notch edge cannot meet a strict lower notch edge. -/
theorem cairns_upper_lower_notch_edges_disjoint
    (P₁ P₂ Q₁ Q₂ : ℂ) (hsep : P₂.im < P₁.im)
    (hupper : ∀ z ∈ segment ℝ P₁ Q₁, P₁.im ≤ z.im)
    (hlower : ∀ z ∈ segment ℝ P₂ Q₂, z.im ≤ P₂.im) :
    Disjoint (segment ℝ P₁ Q₁) (segment ℝ P₂ Q₂) := by
  rw [Set.disjoint_left]
  intro z hzupper hzlower
  have hzord : P₁.im ≤ P₂.im := le_trans (hupper z hzupper) (hlower z hzlower)
  exact (not_le_of_gt hsep) hzord

/-- A nonzero horizontal and vertical edge from one rectangle corner meet only there. -/
theorem cairns_rectangle_corner_edges_meet_at_corner
    (C : ℂ) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    segment ℝ C (C + a) ∩ segment ℝ C (C + b * Complex.I) = {C} := by
  apply segment_inter_eq_endpoint_of_linearIndependent_sub ℝ
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (cairns_horizontal_vertical_linearIndependent a b ha hb)

end HolomorphicAnosov

namespace HolomorphicAnosov

/-- A horizontal rectangle edge and the following vertical edge meet only at their corner. -/
theorem cairns_rectangle_adjacent_edges_meet_at_corner
    (C : ℂ) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    segment ℝ C (C + a) ∩ segment ℝ (C + a) (C + a + b * Complex.I) = {C + a} := by
  rw [segment_symm ℝ C (C + a)]
  apply segment_inter_eq_endpoint_of_linearIndependent_sub ℝ
  have h := cairns_horizontal_vertical_linearIndependent (-a) b (neg_ne_zero.mpr ha) hb
  convert h using 1; simp

end HolomorphicAnosov

namespace HolomorphicAnosov

/-- A vertical rectangle edge followed by a horizontal edge meets only at their corner. -/
theorem cairns_rectangle_vertical_then_horizontal_edges_meet_at_corner
    (C : ℂ) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    segment ℝ C (C + b * Complex.I) ∩
      segment ℝ (C + b * Complex.I) (C + b * Complex.I + a) =
      {C + b * Complex.I} := by
  rw [segment_symm ℝ C (C + b * Complex.I)]
  apply segment_inter_eq_endpoint_of_linearIndependent_sub ℝ
  have h := cairns_vertical_horizontal_linearIndependent a (-b) ha (neg_ne_zero.mpr hb)
  convert h using 1; simp

end HolomorphicAnosov
