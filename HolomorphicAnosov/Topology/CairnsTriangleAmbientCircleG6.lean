import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Tactic.FinCases

open Set
namespace HolomorphicAnosov

/-- The boundary of a nondegenerate triangle is the frontier of its convex hull.
The barycentric coordinates are nonnegative on the hull, strictly positive on its
interior, and one coordinate vanishes precisely on each of the three edges. -/
theorem cairns_triangle_boundary_frontier_g6 (p : Polygon ℂ 3)
    (hi : AffineIndependent ℝ p.vertices) :
    p.boundary ℝ = frontier (convexHull ℝ (range p.vertices)) := by
  let b : AffineBasis (Fin 3) ℝ ℂ :=
    ⟨p.vertices, hi, hi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      simp [Complex.finrank_real_complex])⟩
  have hc := (finite_range b).isCompact_convexHull ℝ
  change p.boundary ℝ = frontier (convexHull ℝ (range b))
  rw [frontier, hc.isClosed.closure_eq, b.interior_convexHull,
    b.convexHull_eq_nonneg_coord]
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    change z ∈ affineSegment ℝ (b i) (b (finRotate 3 i)) at hi
    rw [affineSegment_eq_segment] at hi
    have hh : z ∈ convexHull ℝ (range b) :=
      (convex_convexHull ℝ _).segment_subset
        (subset_convexHull ℝ _ (mem_range_self i))
        (subset_convexHull ℝ _ (mem_range_self (finRotate 3 i))) hi
    refine ⟨by simpa [b.convexHull_eq_nonneg_coord] using hh, ?_⟩
    intro hzpos
    let j := finRotate 3 (finRotate 3 i)
    have hji : j ≠ i := by fin_cases i <;> decide
    have hjr : j ≠ finRotate 3 i := by fin_cases i <;> decide
    have hzero : b.coord j z = 0 := by
      obtain ⟨t, ht, rfl⟩ := (segment_eq_image_lineMap ℝ (b i) (b (finRotate 3 i))) ▸ hi
      rw [AffineMap.apply_lineMap]
      simp only [b.coord_apply, ite_eq_right hji, ite_eq_right hjr]
      simp
    exact (hzpos j).ne' hzero
  · rintro ⟨hz, hn⟩
    have hn' : ∃ j, b.coord j z = 0 := by
      simp only [mem_ofPred_eq, not_forall, not_lt] at hn
      obtain ⟨j, hj⟩ := hn
      exact ⟨j, le_antisymm hj (hz j)⟩
    obtain ⟨j, hj⟩ := hn'
    have hsum := b.sum_coord_apply_eq_one z
    have hrepr := b.linear_combination_coord_eq_self z
    simp only [Fin.sum_univ_three] at hsum hrepr
    fin_cases j
    · change b.coord 0 z = 0 at hj
      rw [hj, zero_smul, zero_add] at hrepr
      rw [hj, zero_add] at hsum
      have hm : z ∈ p.edgeSet ℝ 1 := by
        change z ∈ affineSegment ℝ (b 1) (b 2)
        rw [affineSegment_eq_segment]
        exact ⟨b.coord 1 z, b.coord 2 z, hz 1, hz 2, hsum,
          hrepr⟩
      exact mem_iUnion.mpr ⟨1, hm⟩
    · change b.coord 1 z = 0 at hj
      rw [hj, zero_smul, add_zero] at hrepr
      rw [hj, add_zero] at hsum
      have hm : z ∈ p.edgeSet ℝ 2 := by
        change z ∈ affineSegment ℝ (b 2) (b 0)
        rw [affineSegment_eq_segment]
        exact ⟨b.coord 2 z, b.coord 0 z, hz 2, hz 0,
          by linarith,
          by simpa only [add_comm] using hrepr⟩
      exact mem_iUnion.mpr ⟨2, hm⟩
    · change b.coord 2 z = 0 at hj
      rw [hj, zero_smul, add_zero] at hrepr
      rw [hj, add_zero] at hsum
      have hm : z ∈ p.edgeSet ℝ 0 := by
        change z ∈ affineSegment ℝ (b 0) (b 1)
        rw [affineSegment_eq_segment]
        exact ⟨b.coord 0 z, b.coord 1 z, hz 0, hz 1, hsum,
          hrepr⟩
      exact mem_iUnion.mpr ⟨0, hm⟩

/-- A nondegenerate plane triangle is ambient equivalent to the unit circle.
Apply Mathlib's radial normalization of a bounded convex body to its convex hull. -/
theorem cairns_triangle_ambient_circle_g6 (p : Polygon ℂ 3)
    (hi : AffineIndependent ℝ p.vertices) :
    ∃ H : ℂ ≃ₜ ℂ, H '' p.boundary ℝ = Metric.sphere (0 : ℂ) 1 := by
  let b : AffineBasis (Fin 3) ℝ ℂ :=
    ⟨p.vertices, hi, hi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      simp [Complex.finrank_real_complex])⟩
  obtain ⟨H, _, _, hH⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_convexHull ℝ (range b)) ⟨_, b.centroid_mem_interior_convexHull⟩
    ((finite_range b).isCompact_convexHull ℝ).isBounded
  refine ⟨H, ?_⟩
  rw [cairns_triangle_boundary_frontier_g6 p hi]
  exact hH

end HolomorphicAnosov
