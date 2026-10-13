import HolomorphicAnosov.Topology.CairnsExtremeContactSegmentCoordinates
import Mathlib.Analysis.Convex.Segment

open Set

namespace HolomorphicAnosov

/-- Segments on distinct horizontal lines are disjoint. -/
theorem cairns_horizontal_segments_disjoint
    (A B C D : ℂ) (hAB : A.im = B.im) (hCD : C.im = D.im)
    (hsep : A.im ≠ C.im) : Disjoint (segment ℝ A B) (segment ℝ C D) := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  have h1 := cairns_segment_im_eq_of_endpoints A B z A.im hz1 rfl hAB.symm
  have h2 := cairns_segment_im_eq_of_endpoints C D z C.im hz2 rfl hCD.symm
  exact hsep (h1.symm.trans h2)

/-- Segments on distinct vertical lines are disjoint. -/
theorem cairns_vertical_segments_disjoint
    (A B C D : ℂ) (hAB : A.re = B.re) (hCD : C.re = D.re)
    (hsep : A.re ≠ C.re) : Disjoint (segment ℝ A B) (segment ℝ C D) := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  have h1 := cairns_segment_re_eq_of_endpoints A B z A.re hz1 rfl hAB.symm
  have h2 := cairns_segment_re_eq_of_endpoints C D z C.re hz2 rfl hCD.symm
  exact hsep (h1.symm.trans h2)

end HolomorphicAnosov
