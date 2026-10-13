import Mathlib.Geometry.Polygon.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Topology

open Set Metric

namespace HolomorphicAnosov

/-- Near an interior point of a nondegenerate straight segment in the complex
plane, membership in the segment is exactly vanishing of the oriented area.
Agent-written detail of Cairns (1951), Theorem 2.1, p.860, local straight-edge geometry.
Normalize the endpoints to 0 and 1. The real part of the normalized coordinate
stays strictly between 0 and 1 near the given interior point; within this strip,
vanishing imaginary part is exactly segment membership. Multiplication by the
positive squared length converts the imaginary coordinate to oriented area. -/
theorem segment_local_line {a b x : ℂ} (hab : a ≠ b)
    (hx : x ∈ openSegment ℝ a b) :
    ∃ ε > 0, ∀ z ∈ ball x ε,
      z ∈ segment ℝ a b ↔ (star (b - a) * (z - a)).im = 0 := by
  let v := b - a
  have hv : v ≠ 0 := sub_ne_zero.mpr hab.symm
  let T : ℂ → ℂ := fun z ↦ (z - a) / v
  have hT : Continuous T := (continuous_id.sub continuous_const).div_const v
  have hTline (r : ℝ) : T (a + r • (b - a)) = (r : ℂ) := by
    dsimp [T, v]
    rw [add_sub_cancel_left]
    exact mul_div_cancel_right₀ _ hv
  obtain ⟨r, hr, rfl⟩ := (openSegment_eq_image' ℝ a b) ▸ hx
  have hstrip : {z : ℂ | (T z).re ∈ Ioo (0 : ℝ) 1} ∈
      nhds (a + r • (b - a)) := by
    apply (isOpen_Ioo.preimage (Complex.continuous_re.comp hT)).mem_nhds
    change (T (a + r • (b - a))).re ∈ Ioo (0 : ℝ) 1
    simpa only [hTline, Complex.ofReal_re] using hr
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hstrip
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have hreal := hball hz
  have hdet : (star v * (z - a)).im = Complex.normSq v * (T z).im := by
    have hzv : z - a = T z * v := (div_mul_cancel₀ _ hv).symm
    rw [hzv]
    calc
      (star v * (T z * v)).im = ((star v * v) * T z).im := by congr 1; ring
      _ = Complex.normSq v * (T z).im := by
        change ((starRingEnd ℂ v * v) * T z).im = _
        rw [Complex.conj_mul', ← Complex.ofReal_pow]
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, add_zero, Complex.normSq_eq_norm_sq]
  have hnorm : 0 < Complex.normSq v := Complex.normSq_pos.mpr hv
  constructor
  · intro hzseg
    obtain ⟨s, hs, rfl⟩ := (segment_eq_image' ℝ a b) ▸ hzseg
    change (star v * _).im = 0
    rw [hdet, hTline]
    simp
  · intro hzdet
    have him : (T z).im = 0 := by rw [hdet] at hzdet; exact (mul_eq_zero.mp hzdet).resolve_left (ne_of_gt hnorm)
    have heq : ((T z).re : ℂ) = T z := by
      apply Complex.ext <;> simp [him]
    rw [segment_eq_image' ℝ a b]
    refine ⟨(T z).re, ⟨hreal.1.le, hreal.2.le⟩, ?_⟩
    change a + ((T z).re : ℂ) * (b - a) = z
    rw [heq]
    change a + T z * v = z
    rw [div_mul_cancel₀ _ hv]
    exact add_sub_cancel _ _

/-- A simple polygon agrees locally with the supporting line at every interior
point of an edge. Agent-written detail of Cairns (1951), Theorem 2.1, p.860. Distinct polygon
edges meet the selected edge only at common endpoints. Its interior point is
therefore outside the finite union of all other compact edges. Intersect that
open complement with the straight-segment neighborhood from `segment_local_line`.
No polygon separation theorem is used. -/
theorem polygon_edge_local_line {n : ℕ} (p : Polygon ℂ n)
    (hne : p.HasNondegenerateEdges)
    (hsimple : ∀ i j : Fin n, i ≠ j →
      p.edgeSet ℝ i ∩ p.edgeSet ℝ j ⊆
        p.vertices '' ({i, finRotate n i} ∩ {j, finRotate n j}))
    (i : Fin n) {x : ℂ} (hx : x ∈ openSegment ℝ (p i) (p (finRotate n i))) :
    ∃ ε > 0, ∀ z ∈ ball x ε,
      z ∈ p.boundary ℝ ↔
        (star (p (finRotate n i) - p i) * (z - p i)).im = 0 := by
  classical
  have hab : p i ≠ p (finRotate n i) := hne i
  have hxleft : x ≠ p i := by
    intro heq
    exact hab ((left_mem_openSegment_iff.mp (heq ▸ hx)))
  have hxright : x ≠ p (finRotate n i) := by
    intro heq
    exact hab ((right_mem_openSegment_iff.mp (heq ▸ hx)))
  have hxedge : x ∈ p.edgeSet ℝ i := by
    simpa only [Polygon.edgeSet, affineSegment_eq_segment] using openSegment_subset_segment ℝ _ _ hx
  let F : Set ℂ := ⋃ j : {j : Fin n // j ≠ i}, p.edgeSet ℝ j.val
  have hFclosed : IsClosed F := by
    apply isClosed_iUnion_of_finite
    intro j
    rw [Polygon.edgeSet, affineSegment_eq_segment]
    rw [← convexHull_pair]
    exact ((Set.finite_singleton (p (finRotate n j.val))).insert (p j.val)).isCompact_convexHull ℝ |>.isClosed
  have hxF : x ∉ F := by
    rintro hxF
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxF
    obtain ⟨k, hk, hkx⟩ := hsimple i j.val j.property.symm ⟨hxedge, hj⟩
    rcases hk.1 with rfl | hk
    · exact hxleft hkx.symm
    · exact hxright (hkx.symm.trans (congrArg p (mem_singleton_iff.mp hk)))
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.mem_nhds_iff.mp (hFclosed.isOpen_compl.mem_nhds hxF)
  obtain ⟨ε₂, hε₂, hball₂⟩ := segment_local_line hab hx
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro z hz
  have hz₁ := hball₁ (ball_subset_ball (min_le_left _ _) hz)
  have hz₂ := hball₂ z (ball_subset_ball (min_le_right _ _) hz)
  constructor
  · intro hzboundary
    obtain ⟨j, hj⟩ := mem_iUnion.mp hzboundary
    have hji : j = i := by
      by_contra hne
      exact hz₁ (mem_iUnion.mpr ⟨⟨j, hne⟩, hj⟩)
    subst j
    exact hz₂.mp (by simpa only [Polygon.edgeSet, affineSegment_eq_segment] using hj)
  · intro hzdet
    exact mem_iUnion.mpr ⟨i, by
      simpa only [Polygon.edgeSet, affineSegment_eq_segment] using hz₂.mpr hzdet⟩

end HolomorphicAnosov

