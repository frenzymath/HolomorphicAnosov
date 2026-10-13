import HolomorphicAnosov.Geometry.LyubichMarkedTriangleAffineIndependentG12
import HolomorphicAnosov.Geometry.IdealDiskKleinSide
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Convex.Strict.Extreme
import HolomorphicAnosov.Geometry.IdealTriangleReflectionHalfspaceNormHelpersG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionHalfspaceSignG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionInvolutionG6
import HolomorphicAnosov.Geometry.LyubichItineraryDiskPreservation
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import HolomorphicAnosov.Analysis.Complex.HolomorphicEmbeddingInverse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import HolomorphicAnosov.Analysis.SchwarzRealBoundaryExtension
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.OpenPartialHomeomorph.Basic

noncomputable section

/-! Geometric boundary facts for the marked ideal triangle. (Lyubich, §2.4.4 and §2.4.13) -/

noncomputable section
namespace HolomorphicAnosov

/-- The vertices of a marked ideal triangle form an affine basis of the plane. -/
def MarkedIdealDiskTriangle.affineBasis (T : MarkedIdealDiskTriangle) :
    AffineBasis (Fin 3) ℝ ℂ :=
  ⟨T.vertex, markedIdealDiskTriangle_vertices_affineIndependent T, by
    apply ((markedIdealDiskTriangle_vertices_affineIndependent T).affineSpan_eq_top_iff_card_eq_finrank_add_one).2
    simp [Complex.finrank_real_complex]⟩

/-- Forget only the cyclic marking, retaining the same three distinct ideal vertices for the native reflection-tiling carrier. -/
def MarkedIdealDiskTriangle.vertexTriple (T : MarkedIdealDiskTriangle) :
    IdealDiskTriangle.VertexTriple :=
  ⟨Finset.univ.image T.vertex, by
    classical
    constructor
    · rw [Finset.card_image_of_injective _ T.distinct]
      rfl
    · intro p hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact T.norm_vertex i⟩

/-- The marked Klein edge and the native circle-equation edge are the same literal set. (Lyubich, §2.4.4) -/
theorem MarkedIdealDiskTriangle.openSide_eq_native
    (T : MarkedIdealDiskTriangle) (i j : Fin 3) (hij : i ≠ j) :
    T.openSide i j = IdealDiskTriangle.openSide (T.vertex i) (T.vertex j) := by
  ext z
  constructor
  · intro hz
    exact ⟨hz.1, (idealDiskKlein_mem_openSegment_iff_sideEquation
      (T.norm_vertex i) (T.norm_vertex j) (T.distinct.ne hij) hz.1).mp hz.2⟩
  · intro hz
    exact ⟨hz.1, (idealDiskKlein_mem_openSegment_iff_sideEquation
      (T.norm_vertex i) (T.norm_vertex j) (T.distinct.ne hij) hz.1).mpr hz.2⟩

/-- Every complete open geodesic side belongs to the closed marked triangle. -/
theorem MarkedIdealDiskTriangle.openSide_subset_closedSet
    (T : MarkedIdealDiskTriangle) (i j : Fin 3) : T.openSide i j ⊆ T.closedSet := by
  intro z hz
  exact ⟨hz.1.le, segment_subset_convexHull (Set.mem_range_self i)
    (Set.mem_range_self j) (openSegment_subset_segment ℝ _ _ hz.2)⟩

/-- A side point is outside the triangle interior: its third affine coordinate is zero, whereas every coordinate is strictly positive in the simplex interior. -/
theorem MarkedIdealDiskTriangle.openSide_not_mem_interiorSet
    (T : MarkedIdealDiskTriangle) (i j : Fin 3) {z : ℂ} (hz : z ∈ T.openSide i j) :
    z ∉ T.interiorSet := by
  intro hi
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> decide
  let B := T.affineBasis
  have hpos : 0 < B.coord k (idealDiskKlein z) := by
    have hmem : idealDiskKlein z ∈ interior (convexHull ℝ (Set.range B)) := hi.2
    rw [B.interior_convexHull] at hmem
    exact hmem k
  have hzero : B.coord k (idealDiskKlein z) = 0 := by
    have himg := Set.mem_image_of_mem (B.coord k)
      (openSegment_subset_segment ℝ _ _ hz.2)
    rw [image_segment] at himg
    change B.coord k (idealDiskKlein z) ∈ segment ℝ (B.coord k (B i))
      (B.coord k (B j)) at himg
    simpa [B.coord_apply_ne hki, B.coord_apply_ne hkj] using himg
  linarith

/-- Each marked vertex lies in the filled closed triangle: the Klein map fixes the unit circle, and a vertex belongs to its own convex hull. -/
theorem MarkedIdealDiskTriangle.vertex_mem_closedSet
    (T : MarkedIdealDiskTriangle) (i : Fin 3) : T.vertex i ∈ T.closedSet := by
  refine ⟨(T.norm_vertex i).le, ?_⟩
  have hfix : idealDiskKlein (T.vertex i) = T.vertex i := by
    simp [idealDiskKlein, T.norm_vertex i]
    ring
  rw [hfix]
  exact subset_convexHull ℝ (Set.range T.vertex) (Set.mem_range_self i)

/-- The closed triangle meets the unit circle only at its marked vertices. -/
theorem MarkedIdealDiskTriangle.closedSet_unit_norm_iff
    (T : MarkedIdealDiskTriangle) {z : ℂ} (hz : z ∈ T.closedSet) :
    ‖z‖ = 1 ↔ ∃ i : Fin 3, z = T.vertex i := by
  constructor
  · intro hn
    have hfix : idealDiskKlein z = z := by
      simp [idealDiskKlein, hn]
      ring
    have hzh : z ∈ convexHull ℝ (Set.range T.vertex) := hfix ▸ hz.2
    have hsub : convexHull ℝ (Set.range T.vertex) ⊆ Metric.closedBall (0 : ℂ) 1 := by
      apply convexHull_min
      · rintro w ⟨i, rfl⟩
        simp [Metric.mem_closedBall, dist_zero_right, T.norm_vertex i]
      · exact convex_closedBall _ _
    have hze : z ∈ Set.extremePoints ℝ (Metric.closedBall (0 : ℂ) 1) := by
      rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
      simpa [Metric.mem_sphere, dist_zero_right] using hn
    have hzhExtreme := inter_extremePoints_subset_extremePoints_of_subset hsub ⟨hzh, hze⟩
    obtain ⟨i, hi⟩ := extremePoints_convexHull_subset hzhExtreme
    exact ⟨i, hi.symm⟩
  · rintro ⟨i, rfl⟩
    exact T.norm_vertex i

/-- Klein coordinates preserve the open unit disk, since 2r/(1+r²)<1 for 0≤r<1. -/
theorem idealDiskKlein_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    ‖idealDiskKlein z‖ < 1 := by
  have hs : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  rw [idealDiskKlein, norm_div, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, div_lt_one hs]
  nlinarith [sq_pos_of_pos (sub_pos.mpr hz)]

/-- Every disk point of the closed marked triangle is interior or lies on an open side. -/
theorem MarkedIdealDiskTriangle.closedSet_disk_partition
    (T : MarkedIdealDiskTriangle) {z : ℂ} (hz : z ∈ T.closedSet) (hzd : ‖z‖ < 1) :
    z ∈ T.interiorSet ∨ ∃ i j : Fin 3, i ≠ j ∧ z ∈ T.openSide i j := by
  classical
  let B := T.affineBasis
  let w := idealDiskKlein z
  have hw : ‖w‖ < 1 := idealDiskKlein_norm_lt_one hzd
  have hn : ∀ i, 0 ≤ B.coord i w := by
    have hm : w ∈ convexHull ℝ (Set.range B) := hz.2
    rwa [B.convexHull_eq_nonneg_coord] at hm
  by_cases hp : ∀ i, 0 < B.coord i w
  · left
    refine ⟨hzd, ?_⟩
    change w ∈ interior (convexHull ℝ (Set.range B))
    rwa [B.interior_convexHull]
  · right
    push Not at hp
    obtain ⟨k, hk⟩ := hp
    have hk0 : B.coord k w = 0 := le_antisymm hk (hn k)
    have hs := B.sum_coord_apply_eq_one w
    have he : ∑ i : Fin 3, B.coord i w • T.vertex i = w :=
      B.linear_combination_coord_eq_self w
    have side (i j : Fin 3) (hij : i ≠ j)
        (hsij : B.coord i w + B.coord j w = 1)
        (heij : B.coord i w • T.vertex i + B.coord j w • T.vertex j = w) :
        ∃ i j : Fin 3, i ≠ j ∧ z ∈ T.openSide i j := by
      have hpi : 0 < B.coord i w := by
        apply lt_of_le_of_ne (hn i)
        intro hi
        have hj : B.coord j w = 1 := by linarith
        have hwj : w = T.vertex j := by simpa [← hi, hj] using heij.symm
        rw [hwj, T.norm_vertex j] at hw
        exact (lt_irrefl 1) hw
      have hpj : 0 < B.coord j w := by
        apply lt_of_le_of_ne (hn j)
        intro hj
        have hi : B.coord i w = 1 := by linarith
        have hwi : w = T.vertex i := by simpa [← hj, hi] using heij.symm
        rw [hwi, T.norm_vertex i] at hw
        exact (lt_irrefl 1) hw
      exact ⟨i, j, hij, hzd, B.coord i w, B.coord j w, hpi, hpj, hsij, heij⟩
    fin_cases k
    · change B.coord 0 w = 0 at hk0
      apply side 1 2 (by decide)
      · simpa only [Fin.sum_univ_three, hk0, zero_add, add_zero] using hs
      · simpa only [Fin.sum_univ_three, hk0, zero_smul, zero_add, add_zero] using he
    · change B.coord 1 w = 0 at hk0
      apply side 0 2 (by decide)
      · simpa only [Fin.sum_univ_three, hk0, zero_add, add_zero] using hs
      · simpa only [Fin.sum_univ_three, hk0, zero_smul, zero_add, add_zero] using he
    · change B.coord 2 w = 0 at hk0
      apply side 0 1 (by decide)
      · simpa only [Fin.sum_univ_three, hk0, zero_add, add_zero] using hs
      · simpa only [Fin.sum_univ_three, hk0, zero_smul, zero_add, add_zero] using he

/-- Once closure is identified with the filled triangle, every open edge is in its frontier, by the affine-coordinate exclusion of interior points. -/
theorem MarkedIdealDiskTriangle.openSide_subset_frontier
    (T : MarkedIdealDiskTriangle)
    (hclosure : closure T.interiorSet = T.closedSet)
    (hopen : IsOpen T.interiorSet) (i j : Fin 3) :
    T.openSide i j ⊆ frontier T.interiorSet := by
  intro z hz
  rw [hopen.frontier_eq, hclosure]
  exact ⟨T.openSide_subset_closedSet i j hz,
    T.openSide_not_mem_interiorSet i j hz⟩

/-- An injective marked sphere extension has finite values different from zero and one at every disk point of the closed triangle. -/
theorem MarkedIdealDiskTriangle.sphere_extension_disk_value
    (T : MarkedIdealDiskTriangle) (b : ℂ → OnePoint ℂ)
    (hbinj : Set.InjOn b T.closedSet)
    (hb0 : b (T.vertex 0) = ((0 : ℂ) : OnePoint ℂ))
    (hb1 : b (T.vertex 1) = ((1 : ℂ) : OnePoint ℂ))
    (hb2 : b (T.vertex 2) = OnePoint.infty)
    {z : ℂ} (hz : z ∈ T.closedSet) (hzd : ‖z‖ < 1) :
    ∃ w : ℂ, b z = (w : OnePoint ℂ) ∧ w ≠ 0 ∧ w ≠ 1 := by
  have hne (i : Fin 3) : b z ≠ b (T.vertex i) := by
    intro he
    have hez := hbinj hz (T.vertex_mem_closedSet i) he
    rw [hez, T.norm_vertex i] at hzd
    exact (lt_irrefl 1) hzd
  obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp (by simpa [hb2] using hne 2)
  refine ⟨w, hw.symm, ?_, ?_⟩
  · intro he
    apply hne 0
    rw [← hw, he, hb0]
  · intro he
    apply hne 1
    rw [← hw, he, hb1]

/-- An open edge has a strictly positive coordinate at either endpoint: the corresponding affine coordinate maps the edge into the interval (0,1). -/
theorem MarkedIdealDiskTriangle.openSide_left_coord_pos
    (T : MarkedIdealDiskTriangle) (i j : Fin 3) (hij : i ≠ j)
    {z : ℂ} (hz : z ∈ T.openSide i j) :
    0 < T.affineBasis.coord i (idealDiskKlein z) := by
  let B := T.affineBasis
  have hm := Set.mem_image_of_mem (B.coord i) hz.2
  rw [image_openSegment] at hm
  change B.coord i (idealDiskKlein z) ∈ openSegment ℝ (B.coord i (B i)) (B.coord i (B j)) at hm
  rw [B.coord_apply_eq, B.coord_apply_ne hij, openSegment_symm,
    openSegment_eq_Ioo (by norm_num : (0 : ℝ) < 1)] at hm
  exact hm.1

/-- Where the other two Klein coordinates are positive, membership in the marked interior is exactly positivity of the remaining coordinate. -/
theorem MarkedIdealDiskTriangle.interiorSet_iff_coord
    (T : MarkedIdealDiskTriangle) (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hi : 0 < T.affineBasis.coord i (idealDiskKlein z))
    (hj : 0 < T.affineBasis.coord j (idealDiskKlein z)) :
    z ∈ T.interiorSet ↔ 0 < T.affineBasis.coord k (idealDiskKlein z) := by
  let B := T.affineBasis
  change (‖z‖ < 1 ∧ idealDiskKlein z ∈ interior (convexHull ℝ (Set.range B))) ↔ _
  rw [B.interior_convexHull]
  constructor
  · intro hm
    exact hm.2 k
  · intro hk
    refine ⟨hz, ?_⟩
    intro l
    have hl : l = i ∨ l = j ∨ l = k := by omega
    rcases hl with rfl | rfl | rfl <;> assumption

/-- The corresponding closed-carrier condition allows the remaining coordinate to vanish, since the other two are already positive. -/
theorem MarkedIdealDiskTriangle.closedSet_iff_coord
    (T : MarkedIdealDiskTriangle) (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hi : 0 < T.affineBasis.coord i (idealDiskKlein z))
    (hj : 0 < T.affineBasis.coord j (idealDiskKlein z)) :
    z ∈ T.closedSet ↔ 0 ≤ T.affineBasis.coord k (idealDiskKlein z) := by
  let B := T.affineBasis
  change (‖z‖ ≤ 1 ∧ idealDiskKlein z ∈ convexHull ℝ (Set.range B)) ↔ _
  rw [B.convexHull_eq_nonneg_coord]
  constructor
  · intro hm
    exact hm.2 k
  · intro hk
    refine ⟨hz.le, ?_⟩
    intro l
    have hl : l = i ∨ l = j ∨ l = k := by omega
    rcases hl with rfl | rfl | rfl
    · exact hi.le
    · exact hj.le
    · exact hk

end HolomorphicAnosov


/-! Linear half-space equations in Klein coordinates. (Lyubich, §2.4.4) -/

noncomputable section
open scoped ComplexConjugate
namespace HolomorphicAnosov
open IdealDiskTriangle

/-- The real part of multiplication by a fixed complex number is real linear. -/
def realMulLinear (c : ℂ) : ℂ →ₗ[ℝ] ℝ where
  toFun z := (z * c).re
  map_add' x y := by simp [add_mul]
  map_smul' a z := by simp [Complex.real_smul, mul_assoc]

/-- The imaginary part of a fixed complex quotient is real linear. -/
def imagDivLinear (p : ℂ) : ℂ →ₗ[ℝ] ℝ where
  toFun z := (z / p).im
  map_add' x y := by simp [add_div]
  map_smul' a z := by simp [Complex.real_smul, mul_div_assoc]

/-- The chord functional: a diameter has its usual line equation, while a non-diameter chord has equation 1-Re(z conj c), with c its circle center. -/
def kleinSideFunctional (p q : ℂ) : ℂ →ᵃ[ℝ] ℝ :=
  if p + q = 0 then (imagDivLinear p).toAffineMap
  else AffineMap.const ℝ ℂ 1 - (realMulLinear (conj (orthogonalCenter p q))).toAffineMap

/-- Multiplication by the positive Klein radial factor turns the chord functional into the original geodesic side equation. -/
theorem sideEquation_klein_functional (p q z : ℂ) :
    sideEquation p q z =
      (if p + q = 0 then (1 + ‖z‖ ^ 2) / 2 else 1 + ‖z‖ ^ 2) *
        kleinSideFunctional p q (idealDiskKlein z) := by
  have hd : (1 + ‖z‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hk : idealDiskKlein z = ((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * z := by
    unfold idealDiskKlein
    push_cast
    ring
  by_cases ha : p + q = 0
  · simp only [sideEquation, kleinSideFunctional, ite_eq_left ha]
    change (z / p).im = (1 + ‖z‖ ^ 2) / 2 * (idealDiskKlein z / p).im
    rw [hk, mul_div_assoc]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    field_simp
  · simp only [sideEquation, kleinSideFunctional, ite_eq_right ha]
    change ‖z - orthogonalCenter p q‖ ^ 2 - (‖orthogonalCenter p q‖ ^ 2 - 1) =
      (1 + ‖z‖ ^ 2) * (1 - (idealDiskKlein z * conj (orthogonalCenter p q)).re)
    rw [hk, mul_assoc]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← Complex.normSq_eq_norm_sq (z - orthogonalCenter p q), Complex.normSq_sub,
      Complex.normSq_eq_norm_sq z, Complex.normSq_eq_norm_sq (orthogonalCenter p q)]
    field_simp
    simp only [Complex.mul_re]
    ring

/-- Both ideal endpoints satisfy their geodesic equation, including the antipodal diameter case. -/
theorem sideEquation_left_endpoint {p q : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    sideEquation p q p = 0 := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  by_cases ha : p + q = 0
  · simp [sideEquation, ha, hp0]
  · have he := idealTriangle_sideEquation_denominator_normSq_g6 (z := p) hp hq ha
    have hpunit : p * conj p = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp]
      norm_num
    have hden : 2 - (p + q) * conj p = (p - q) * conj p := by
      linear_combination -2 * hpunit
    rw [hden, Complex.normSq_mul, Complex.normSq_conj,
      Complex.normSq_eq_norm_sq p, hp] at he
    have hsum : Complex.normSq (p - q) + Complex.normSq (p + q) = 4 := by
      rw [Complex.normSq_sub, Complex.normSq_add,
        Complex.normSq_eq_norm_sq p, Complex.normSq_eq_norm_sq q, hp, hq]
      ring
    have hn : Complex.normSq (p + q) ≠ 0 := (Complex.normSq_pos.mpr ha).ne'
    apply (mul_eq_zero.mp (show Complex.normSq (p + q) * sideEquation p q p = 0 by
      nlinarith)).resolve_left hn

/-- The chord functional vanishes at its first unit endpoint. -/
theorem kleinSideFunctional_left_endpoint {p q : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) : kleinSideFunctional p q p = 0 := by
  have he := sideEquation_klein_functional p q p
  have hk : idealDiskKlein p = p := by simp [idealDiskKlein, hp]; ring
  rw [hk, hp, sideEquation_left_endpoint hp hq] at he
  split_ifs at he <;> nlinarith

/-- Swapping the two endpoints leaves the non-diameter chord functional unchanged; in the diameter case both endpoints have zero imaginary quotient. -/
theorem kleinSideFunctional_right_endpoint {p q : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) : kleinSideFunctional p q q = 0 := by
  by_cases ha : p + q = 0
  · have hqneg : q = -p := eq_neg_of_add_eq_zero_right ha
    have hp0 : p ≠ 0 := by intro h; simp [h] at hp
    simp [kleinSideFunctional, imagDivLinear, hqneg, hp0]
  · have he := kleinSideFunctional_left_endpoint hq hp
    have hc : orthogonalCenter q p = orthogonalCenter p q := by
      unfold orthogonalCenter
      congr 1 <;> ring
    simpa only [kleinSideFunctional, add_comm q p, ite_eq_right ha, hc] using he

/-- The chord functional is nonzero. -/
theorem kleinSideFunctional_not_zero {p q : ℂ} (hp : ‖p‖ = 1) :
    ∃ z : ℂ, kleinSideFunctional p q z ≠ 0 := by
  by_cases ha : p + q = 0
  · have hp0 : p ≠ 0 := by intro h; simp [h] at hp
    refine ⟨p * Complex.I, ?_⟩
    simp [kleinSideFunctional, ha, imagDivLinear, mul_comm p Complex.I, hp0]
  · exact ⟨0, by simp [kleinSideFunctional, ha, realMulLinear]⟩

/-- The functional vanishing on two vertices of a planar affine basis is its value at the third vertex times that third barycentric coordinate. -/
theorem kleinSideFunctional_eq_coord
    (B : AffineBasis (Fin 3) ℝ ℂ) (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (hi : ‖B i‖ = 1) (hj : ‖B j‖ = 1) :
    kleinSideFunctional (B i) (B j) =
      kleinSideFunctional (B i) (B j) (B k) • B.coord k := by
  apply AffineMap.ext_on B.tot
  rintro _ ⟨l, rfl⟩
  change kleinSideFunctional (B i) (B j) (B l) =
    kleinSideFunctional (B i) (B j) (B k) * B.coord k (B l)
  have hl : l = i ∨ l = j ∨ l = k := by omega
  rcases hl with rfl | rfl | rfl
  · rw [kleinSideFunctional_left_endpoint hi hj, B.coord_apply_ne hki, mul_zero]
  · rw [kleinSideFunctional_right_endpoint hi hj, B.coord_apply_ne hjk.symm, mul_zero]
  · rw [B.coord_apply_eq, mul_one]

/-- The third unit vertex is strictly off the first two vertices' chord. -/
theorem kleinSideFunctional_third_ne_zero
    (B : AffineBasis (Fin 3) ℝ ℂ) (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (hi : ‖B i‖ = 1) (hj : ‖B j‖ = 1) :
    kleinSideFunctional (B i) (B j) (B k) ≠ 0 := by
  intro hz
  have he := kleinSideFunctional_eq_coord B i j k hij hjk hki hi hj
  obtain ⟨z, hzne⟩ := kleinSideFunctional_not_zero (q := B j) hi
  apply hzne
  have hev := congrArg (fun f : ℂ →ᵃ[ℝ] ℝ ↦ f z) he
  change kleinSideFunctional (B i) (B j) z =
    kleinSideFunctional (B i) (B j) (B k) * B.coord k z at hev
  simpa only [hz, zero_mul] using hev

/-- Each native half-disk inequality is exactly nonnegativity of the opposite Klein barycentric coordinate. -/
theorem sideEquation_product_coord_factor
    (B : AffineBasis (Fin 3) ℝ ℂ) (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (hi : ‖B i‖ = 1) (hj : ‖B j‖ = 1) (hk : ‖B k‖ = 1) (z : ℂ) :
    ∃ a : ℝ, 0 < a ∧ sideEquation (B i) (B j) z * sideEquation (B i) (B j) (B k) =
      a * B.coord k (idealDiskKlein z) := by
  let a : ℂ → ℝ := fun x ↦
    if B i + B j = 0 then (1 + ‖x‖ ^ 2) / 2 else 1 + ‖x‖ ^ 2
  let f := kleinSideFunctional (B i) (B j)
  have hap (x : ℂ) : 0 < a x := by dsimp [a]; split_ifs <;> positivity
  have hfn : f (B k) ≠ 0 := kleinSideFunctional_third_ne_zero B i j k hij hjk hki hi hj
  have hlin : f (idealDiskKlein z) = f (B k) * B.coord k (idealDiskKlein z) :=
    congrArg (fun g : ℂ →ᵃ[ℝ] ℝ ↦ g (idealDiskKlein z))
      (kleinSideFunctional_eq_coord B i j k hij hjk hki hi hj)
  have hK : idealDiskKlein (B k) = B k := by simp [idealDiskKlein, hk]; ring
  have hzEq : sideEquation (B i) (B j) z = a z * f (idealDiskKlein z) :=
    sideEquation_klein_functional _ _ _
  have hkEq : sideEquation (B i) (B j) (B k) = a (B k) * f (B k) := by
    simpa only [hK] using sideEquation_klein_functional (B i) (B j) (B k)
  have hfactor : 0 < a z * a (B k) * (f (B k)) ^ 2 :=
    mul_pos (mul_pos (hap z) (hap (B k))) (sq_pos_of_ne_zero hfn)
  refine ⟨a z * a (B k) * (f (B k)) ^ 2, hfactor, ?_⟩
  rw [hzEq, hkEq, hlin]
  ring

/-- Native nonnegative half-space signs are exactly nonnegative Klein barycentric coordinates, by the positive scalar identity. -/
theorem sideEquation_mul_nonneg_iff_coord
    (B : AffineBasis (Fin 3) ℝ ℂ) (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (hi : ‖B i‖ = 1) (hj : ‖B j‖ = 1) (hk : ‖B k‖ = 1) (z : ℂ) :
    0 ≤ sideEquation (B i) (B j) z * sideEquation (B i) (B j) (B k) ↔
      0 ≤ B.coord k (idealDiskKlein z) := by
  obtain ⟨a, ha, he⟩ := sideEquation_product_coord_factor B i j k hij hjk hki hi hj hk z
  rw [he, mul_nonneg_iff_of_pos_left ha]

/-- The same positive scalar identity also identifies the nonpositive signs. -/
theorem sideEquation_mul_nonpos_iff_coord
    (B : AffineBasis (Fin 3) ℝ ℂ) (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (hi : ‖B i‖ = 1) (hj : ‖B j‖ = 1) (hk : ‖B k‖ = 1) (z : ℂ) :
    sideEquation (B i) (B j) z * sideEquation (B i) (B j) (B k) ≤ 0 ↔
      B.coord k (idealDiskKlein z) ≤ 0 := by
  obtain ⟨a, ha, he⟩ := sideEquation_product_coord_factor B i j k hij hjk hki hi hj hk z
  rw [he]
  constructor <;> intro h <;> nlinarith

/-- Vanishing of the opposite Klein coordinate is exactly the side geodesic equation, because the radial factor and third-vertex functional value are both nonzero. -/
theorem klein_coord_zero_iff_sideEquation
    (B : AffineBasis (Fin 3) ℝ ℂ) (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (hi : ‖B i‖ = 1) (hj : ‖B j‖ = 1) (z : ℂ) :
    B.coord k (idealDiskKlein z) = 0 ↔ sideEquation (B i) (B j) z = 0 := by
  have ha : (if B i + B j = 0 then (1 + ‖z‖ ^ 2) / 2 else 1 + ‖z‖ ^ 2 : ℝ) ≠ 0 := by
    split_ifs <;> positivity
  have hf := kleinSideFunctional_third_ne_zero B i j k hij hjk hki hi hj
  have hlin : kleinSideFunctional (B i) (B j) (idealDiskKlein z) =
      kleinSideFunctional (B i) (B j) (B k) * B.coord k (idealDiskKlein z) :=
    congrArg (fun f : ℂ →ᵃ[ℝ] ℝ ↦ f (idealDiskKlein z))
      (kleinSideFunctional_eq_coord B i j k hij hjk hki hi hj)
  rw [sideEquation_klein_functional, hlin]
  simp only [mul_eq_zero, ha, hf, false_or]

/-- The selected side reflection reverses the sign of the opposite Klein barycentric coordinate. -/
theorem klein_coord_reflection_sign
    (B : AffineBasis (Fin 3) ℝ ℂ) (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (hi : ‖B i‖ = 1) (hj : ‖B j‖ = 1) (hk : ‖B k‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (0 ≤ B.coord k (idealDiskKlein (idealDiskSideReflection (B i) (B j) z))) ↔
      B.coord k (idealDiskKlein z) ≤ 0 := by
  rw [← sideEquation_mul_nonneg_iff_coord B i j k hij hjk hki hi hj hk,
    ← sideEquation_mul_nonpos_iff_coord B i j k hij hjk hki hi hj hk]
  exact idealDiskSideReflection_halfspace_sign_g6 hi hj (B.ind.injective.ne hij) hz

/-- Inside the disk the reflection fixes precisely its geodesic side. -/
theorem idealDiskSideReflection_fixed_iff_sideEquation {p q z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) (hz : ‖z‖ < 1) :
    idealDiskSideReflection p q z = z ↔ sideEquation p q z = 0 := by
  constructor
  · intro he
    have hs : sideEquation p q z * sideEquation p q z ≤ 0 :=
      (idealDiskSideReflection_halfspace_sign_g6 (r := z) hp hq hpq hz).mp
        (by rw [he]; exact mul_self_nonneg _)
    nlinarith [sq_nonneg (sideEquation p q z)]
  · intro he
    exact idealDiskSideReflection_fixed_openSide hp hq hpq ⟨hz, he⟩

end HolomorphicAnosov


/-! Analytic formulas for an ideal triangle side reflection. (Lyubich, §2.4.4 and §2.4.13) -/

namespace HolomorphicAnosov
open scoped ComplexConjugate

/-- Conjugation converts the geometric side reflection to a holomorphic fractional-linear map. -/
theorem idealDiskSideReflection_conj_differentiableAt {p q z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (fun w ↦ conj (idealDiskSideReflection p q w)) z := by
  simp only [idealDiskSideReflection, map_div₀, map_sub, map_mul, map_add,
    map_ofNat, Complex.conj_conj]
  exact ((differentiableAt_const _).sub
    ((differentiableAt_const _).mul differentiableAt_id)).div
    ((differentiableAt_const _).sub
      ((differentiableAt_const _).mul differentiableAt_id))
    (IdealDiskTriangle.idealDiskSideReflection_conjugate_denominator_ne_zero_g6 hp hq hz)

/-- Schwarz reflection of a holomorphic function across an ideal disk side is holomorphic away from that side. -/
theorem idealDiskSideReflection_conj_comp_differentiableAt
    {p q z : ℂ} {f : ℂ → ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hz : ‖z‖ < 1)
    (hf : DifferentiableAt ℂ f (idealDiskSideReflection p q z)) :
    DifferentiableAt ℂ (fun w ↦ conj (f (idealDiskSideReflection p q w))) z := by
  have hg : DifferentiableAt ℂ (conj ∘ f ∘ conj)
      (conj (idealDiskSideReflection p q z)) := by
    apply differentiableAt_conj_conj_iff.mpr
    simpa only [Complex.conj_conj] using hf
  simpa only [Function.comp_def, Complex.conj_conj] using
    hg.comp z (idealDiskSideReflection_conj_differentiableAt hp hq hz)

/-- The inverse reflected formula is holomorphic as well: conjugate the composition of the holomorphic function with the conjugated reflection. -/
theorem idealDiskSideReflection_comp_conj_differentiableAt
    {p q z : ℂ} {f : ℂ → ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hz : ‖f (conj z)‖ < 1)
    (hf : DifferentiableAt ℂ f (conj z)) :
    DifferentiableAt ℂ (fun w ↦ idealDiskSideReflection p q (f (conj w))) z := by
  have hg := (idealDiskSideReflection_conj_differentiableAt hp hq hz).comp
    (conj z) hf
  have hh := differentiableAt_conj_conj_iff.mpr hg
  simpa only [Function.comp_def, Complex.conj_conj] using hh

/-- Continuity of the anti-Möbius reflection on the unit disk follows by conjugating its holomorphic conjugate. -/
theorem idealDiskSideReflection_continuousOn {p q : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    ContinuousOn (idealDiskSideReflection p q) {z : ℂ | ‖z‖ < 1} := by
  intro z hz
  have h := Complex.continuous_conj.continuousAt.comp
    (idealDiskSideReflection_conj_differentiableAt hp hq hz).continuousAt
  simpa only [Function.comp_def, Complex.conj_conj] using h.continuousWithinAt

/-- The actual side reflection is a partial homeomorphism of the complex plane with source and target the open unit disk. (Lyubich, §2.4.4) -/
noncomputable def idealDiskSideReflectionPartial (p q : ℂ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) :
    OpenPartialHomeomorph ℂ ℂ where
  toFun := idealDiskSideReflection p q
  invFun := idealDiskSideReflection p q
  source := {z : ℂ | ‖z‖ < 1}
  target := {z : ℂ | ‖z‖ < 1}
  map_source' _ hz := IdealDiskTriangle.idealDiskSideReflection_mem_disk_g6 hp hq hpq hz
  map_target' _ hz := IdealDiskTriangle.idealDiskSideReflection_mem_disk_g6 hp hq hpq hz
  left_inv' _ hz := IdealDiskTriangle.idealDiskSideReflection_involutive_disk_g6 hp hq hpq _ hz
  right_inv' _ hz := IdealDiskTriangle.idealDiskSideReflection_involutive_disk_g6 hp hq hpq _ hz
  open_source := isOpen_lt continuous_norm continuous_const
  open_target := isOpen_lt continuous_norm continuous_const
  continuousOn_toFun := idealDiskSideReflection_continuousOn hp hq
  continuousOn_invFun := idealDiskSideReflection_continuousOn hp hq

end HolomorphicAnosov


/-! Holomorphic coordinates flattening an antiholomorphic involution. (Lyubich, §2.4.13) -/

noncomputable section
namespace HolomorphicAnosov
open Set Filter Complex
open scoped _root_.Topology ComplexConjugate

/-- A holomorphic function with nonzero derivative at x supplies a literal biholomorphic chart near x inside its given open domain. -/
theorem exists_holomorphic_local_chart {U : Set ℂ} (hU : IsOpen U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) {x : ℂ} (hx : x ∈ U)
    (hderiv : deriv f x ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, x ∈ e.source ∧ e.source ⊆ U ∧
      (e : ℂ → ℂ) = f ∧ DifferentiableOn ℂ e e.source ∧
      DifferentiableOn ℂ e.symm e.target := by
  have hstrict : HasStrictDerivAt f (deriv f x) x :=
    ((hf.analyticOnNhd hU x hx).contDiffAt (n := 1)).hasStrictDerivAt (by simp)
  let e₀ := (hstrict.hasStrictFDerivAt_equiv hderiv).toOpenPartialHomeomorph f
  let e := e₀.restrOpen U hU
  have hxe : x ∈ e.source := ⟨(hstrict.hasStrictFDerivAt_equiv hderiv).mem_toOpenPartialHomeomorph_source, hx⟩
  have hsub : e.source ⊆ U := fun _ hz ↦ hz.2
  have heq : (e : ℂ → ℂ) = f := rfl
  have hehol : DifferentiableOn ℂ e e.source := hf.mono hsub
  refine ⟨e, hxe, hsub, heq, hehol, ?_⟩
  intro w hw
  exact (Analysis.Complex.coordinateInverseDeriv e hehol hw).2.differentiableAt.differentiableWithinAt

/-- An antiholomorphic involution has local holomorphic coordinates which intertwine it with conjugation. -/
theorem exists_reflective_holomorphic_coordinate
    (r : OpenPartialHomeomorph ℂ ℂ) (hrt : r.target = r.source)
    (hinv : ∀ z ∈ r.source, r (r z) = z)
    (hhol : DifferentiableOn ℂ (fun z ↦ conj (r z)) r.source)
    {x : ℂ} (hx : x ∈ r.source) (hfix : r x = x)
    (N : Set ℂ) (hN : IsOpen N) (hxN : x ∈ N) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, x ∈ e.source ∧ e.source ⊆ r.source ∧
      e.source ⊆ N ∧ DifferentiableOn ℂ e e.source ∧ DifferentiableOn ℂ e.symm e.target ∧
      (e x).im = 0 ∧
      (∀ z ∈ e.source, r z ∈ e.source) ∧
      (∀ w ∈ e.target, conj w ∈ e.target) ∧
      (∀ z ∈ e.source, e (r z) = conj (e z)) ∧
      ∀ z ∈ e.source, (e z).im = 0 ↔ r z = z := by
  let g : ℂ → ℂ := fun z ↦ conj (r z)
  have hg : DifferentiableAt ℂ g x := hhol.differentiableAt (r.open_source.mem_nhds hx)
  have hrmap {z : ℂ} (hz : z ∈ r.source) : r z ∈ r.source := hrt ▸ r.map_source hz
  have hchoice : ∃ f : ℂ → ℂ, DifferentiableOn ℂ f r.source ∧ deriv f x ≠ 0 ∧
      ∀ z ∈ r.source, f (r z) = conj (f z) := by
    by_cases hplus : 1 + deriv g x ≠ 0
    · refine ⟨fun z ↦ z + g z, differentiableOn_id.add hhol, ?_, ?_⟩
      · have hd : HasDerivAt (fun z : ℂ ↦ z + g z) (1 + deriv g x) x :=
          (hasDerivAt_id x).add hg.hasDerivAt
        rw [hd.deriv]
        exact hplus
      · intro z hz
        simp only [g, hinv z hz, map_add, Complex.conj_conj]
        ring
    · have hminus : Complex.I * (1 - deriv g x) ≠ 0 := by
        have he : deriv g x = -1 := by linear_combination (not_ne_iff.mp hplus)
        simp [he]
      refine ⟨fun z ↦ Complex.I * (z - g z),
        (differentiableOn_const Complex.I).mul (differentiableOn_id.sub hhol), ?_, ?_⟩
      · have hd : HasDerivAt (fun z : ℂ ↦ Complex.I * (z - g z))
            (Complex.I * (1 - deriv g x)) x :=
          ((hasDerivAt_id x).sub hg.hasDerivAt).const_mul Complex.I
        rw [hd.deriv]
        exact hminus
      · intro z hz
        simp only [g, hinv z hz, map_mul, map_sub, Complex.conj_I, Complex.conj_conj]
        ring
  obtain ⟨f, hf, hfd, hfc⟩ := hchoice
  obtain ⟨e₀, hx₀, hs₀, he₀, hf₀, hfi₀⟩ := exists_holomorphic_local_chart
    (r.open_source.inter hN) f (hf.mono Set.inter_subset_left) ⟨hx, hxN⟩ hfd
  let V := e₀.source ∩ (r.source ∩ r ⁻¹' e₀.source)
  have hV : IsOpen V := e₀.open_source.inter (r.isOpen_inter_preimage e₀.open_source)
  let e := e₀.restrOpen V hV
  have hsource : e.source = e₀.source ∩ V := rfl
  have hxe : x ∈ e.source := ⟨hx₀, hx₀, hx, by simpa only [Set.mem_preimage, hfix] using hx₀⟩
  have hsub : e.source ⊆ r.source := fun _ hz ↦ (hs₀ hz.1).1
  have hsubN : e.source ⊆ N := fun _ hz ↦ (hs₀ hz.1).2
  have hef : (e : ℂ → ℂ) = f := he₀
  have hehol : DifferentiableOn ℂ e e.source := by
    rw [hef]
    exact hf.mono hsub
  have heinv : DifferentiableOn ℂ e.symm e.target := by
    intro w hw
    exact (Analysis.Complex.coordinateInverseDeriv e hehol hw).2.differentiableAt.differentiableWithinAt
  have hec (z : ℂ) (hz : z ∈ r.source) : e (r z) = conj (e z) := by
    rw [hef]
    exact hfc z hz
  have hsym (z : ℂ) (hz : z ∈ e.source) : r z ∈ e.source := by
    have hz₀ : z ∈ e₀.source := hz.1
    have hrz₀ : r z ∈ e₀.source := hz.2.2.2
    exact ⟨hrz₀, hrz₀, hrmap (hsub hz), by simpa only [Set.mem_preimage, hinv z (hsub hz)] using hz₀⟩
  have htarget (w : ℂ) (hw : w ∈ e.target) : conj w ∈ e.target := by
    have hys := e.map_target hw
    have hr := e.map_source (hsym (e.symm w) hys)
    rw [hec _ (hsub hys), e.right_inv hw] at hr
    exact hr
  have hreal (z : ℂ) (hz : z ∈ e.source) : (e z).im = 0 ↔ r z = z := by
    constructor
    · intro hi
      apply e.injOn (hsym z hz) hz
      rw [hec z (hsub hz)]
      apply Complex.ext <;> simp [hi]
    · intro hzfix
      have he := congrArg Complex.im (hec z (hsub hz))
      rw [hzfix, Complex.conj_im] at he
      linarith
  exact ⟨e, hxe, hsub, hsubN, hehol, heinv, (hreal x hxe).mpr hfix,
    hsym, htarget, fun z hz ↦ hec z (hsub hz), hreal⟩

/-- The reflective coordinate may be chosen with a round-disk target centered at the real image of the fixed point. -/
theorem exists_reflective_holomorphic_ball_coordinate
    (r : OpenPartialHomeomorph ℂ ℂ) (hrt : r.target = r.source)
    (hinv : ∀ z ∈ r.source, r (r z) = z)
    (hhol : DifferentiableOn ℂ (fun z ↦ conj (r z)) r.source)
    {x : ℂ} (hx : x ∈ r.source) (hfix : r x = x)
    (N : Set ℂ) (hN : IsOpen N) (hxN : x ∈ N) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ ε : ℝ, 0 < ε ∧
      e.target = Metric.ball (e x) ε ∧ x ∈ e.source ∧
      e.source ⊆ r.source ∧ e.source ⊆ N ∧
      DifferentiableOn ℂ e e.source ∧ DifferentiableOn ℂ e.symm e.target ∧
      (e x).im = 0 ∧
      (∀ z ∈ e.source, r z ∈ e.source) ∧
      (∀ w ∈ e.target, conj w ∈ e.target) ∧
      (∀ z ∈ e.source, e (r z) = conj (e z)) ∧
      ∀ z ∈ e.source, (e z).im = 0 ↔ r z = z := by
  obtain ⟨e₀, hx₀, hs₀, hN₀, hehol₀, heinv₀, hxreal, hrs₀, hcs₀, hec₀, haxis₀⟩ :=
    exists_reflective_holomorphic_coordinate r hrt hinv hhol hx hfix N hN hxN
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp
    (e₀.open_target.mem_nhds (e₀.map_source hx₀))
  let B := Metric.ball (e₀ x) ε
  let e := (e₀.symm.restrOpen B Metric.isOpen_ball).symm
  have hes : e.source = e₀.source ∩ e₀ ⁻¹' B := rfl
  have het : e.target = B := by
    change e₀.target ∩ B = B
    exact inter_eq_right.mpr hb
  have hefun : (e : ℂ → ℂ) = e₀ := rfl
  have hxe : x ∈ e.source := ⟨hx₀, Metric.mem_ball_self hε⟩
  have hsub : e.source ⊆ e₀.source := fun _ hz ↦ hz.1
  have hbc {w : ℂ} (hw : w ∈ B) : conj w ∈ B := by
    change dist (conj w) (e₀ x) < ε
    rw [Complex.dist_conj_comm, Complex.conj_eq_iff_im.mpr hxreal]
    exact hw
  have hrse (z : ℂ) (hz : z ∈ e.source) : r z ∈ e.source := by
    refine ⟨hrs₀ z hz.1, ?_⟩
    change e₀ (r z) ∈ B
    rw [hec₀ z hz.1]
    exact hbc hz.2
  have hce (w : ℂ) (hw : w ∈ e.target) : conj w ∈ e.target := by
    rw [het] at hw ⊢
    exact hbc hw
  have hehol : DifferentiableOn ℂ e e.source := hehol₀.mono hsub
  have heinv : DifferentiableOn ℂ e.symm e.target := by
    intro w hw
    exact (Analysis.Complex.coordinateInverseDeriv e hehol hw).2.differentiableAt.differentiableWithinAt
  refine ⟨e, ε, hε, het, hxe, hs₀.trans' hsub, hN₀.trans' hsub, hehol, heinv,
    hxreal, hrse, hce, ?_, ?_⟩
  · intro z hz
    exact hec₀ z hz.1
  · intro z hz
    exact haxis₀ z hz.1

/-- Equivariance of a partial homeomorphism passes to its literal inverse on the target, provided the source and target are reflection invariant. -/
theorem reflective_coordinate_inverse
    (e : OpenPartialHomeomorph ℂ ℂ) (r : ℂ → ℂ)
    (hrs : ∀ z ∈ e.source, r z ∈ e.source)
    (hct : ∀ w ∈ e.target, conj w ∈ e.target)
    (hec : ∀ z ∈ e.source, e (r z) = conj (e z))
    {w : ℂ} (hw : w ∈ e.target) : e.symm (conj w) = r (e.symm w) := by
  apply e.injOn (e.map_target (hct w hw)) (hrs _ (e.map_target hw))
  rw [e.right_inv (hct w hw), hec _ (e.map_target hw), e.right_inv hw]

end HolomorphicAnosov


/-! Orienting a flattened reflection side. (Lyubich, §2.4.13) -/

namespace HolomorphicAnosov
open Set
open scoped ComplexConjugate

/-- A continuous nonvanishing real function has one strict sign on a preconnected set, by the intermediate value theorem. -/
theorem preconnected_nonzero_sign {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsPreconnected S) (f : X → ℝ)
    (hf : ContinuousOn f S) (hne : ∀ x ∈ S, f x ≠ 0) :
    (∀ x ∈ S, 0 < f x) ∨ (∀ x ∈ S, f x < 0) := by
  by_cases hp : ∃ x ∈ S, 0 < f x
  · left
    obtain ⟨x, hx, hpx⟩ := hp
    intro y hy
    by_contra hpy
    have hny : f y < 0 := lt_of_le_of_ne (le_of_not_gt hpy) (hne y hy)
    obtain ⟨z, hz, hfz⟩ := hS.intermediate_value hy hx hf ⟨hny.le, hpx.le⟩
    exact hne z hz hfz
  · right
    intro y hy
    exact lt_of_le_of_ne (le_of_not_gt (fun hp' ↦ hp ⟨y, hy, hp'⟩)) (hne y hy)

/-- A real defining function with precisely the real axis as zero set and reflection-reversed sign defines either the upper or lower half of a symmetric neighborhood. -/
theorem reflected_defining_function_orientation
    (U : Set ℂ) (hconj : ∀ z ∈ U, conj z ∈ U)
    (hconn : IsPreconnected (U ∩ {z : ℂ | 0 < z.im}))
    (f : ℂ → ℝ) (hf : ContinuousOn f U)
    (hzero : ∀ z ∈ U, f z = 0 ↔ z.im = 0)
    (hflip : ∀ z ∈ U, 0 ≤ f (conj z) ↔ f z ≤ 0) :
    (∀ z ∈ U, 0 < f z ↔ 0 < z.im) ∨
      (∀ z ∈ U, 0 < f z ↔ z.im < 0) := by
  have hne (z : ℂ) (hz : z ∈ U ∩ {z : ℂ | 0 < z.im}) : f z ≠ 0 := by
    intro he
    have hi := (hzero z hz.1).mp he
    have hp : 0 < z.im := hz.2
    linarith
  rcases preconnected_nonzero_sign hconn f (hf.mono inter_subset_left) hne with hpos | hneg
  · left
    intro z hz
    constructor
    · intro hpf
      by_contra hpi
      have hle : z.im ≤ 0 := le_of_not_gt hpi
      rcases hle.eq_or_lt with he | hn
      · have he0 := (hzero z hz).mpr he
        linarith
      · have hcp : 0 < (conj z).im := by simpa only [Complex.conj_im] using neg_pos.mpr hn
        have hfp := hpos (conj z) ⟨hconj z hz, hcp⟩
        have hfn := (hflip z hz).mp hfp.le
        linarith
    · intro hpi
      exact hpos z ⟨hz, hpi⟩
  · right
    intro z hz
    constructor
    · intro hpf
      by_contra hni
      have hle : 0 ≤ z.im := le_of_not_gt hni
      rcases hle.eq_or_lt with he | hp
      · have he0 := (hzero z hz).mpr he.symm
        linarith
      · have hfn := hneg z ⟨hz, hp⟩
        linarith
    · intro hni
      have hcp : 0 < (conj z).im := by simpa only [Complex.conj_im] using neg_pos.mpr hni
      have hcn := hneg (conj z) ⟨hconj z hz, hcp⟩
      exact lt_of_not_ge (fun hle ↦ (not_le_of_gt hcn) ((hflip z hz).mpr hle))

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set Complex
open scoped ComplexConjugate

/-- The rational Klein coordinate is continuous on the entire complex plane, since its real denominator 1+‖z‖² is everywhere positive. -/
theorem continuous_idealDiskKlein : Continuous idealDiskKlein := by
  unfold idealDiskKlein
  apply Continuous.div₀ (by fun_prop) (by fun_prop)
  intro z
  exact_mod_cast (ne_of_gt (by positivity : 0 < 1 + ‖z‖ ^ 2))

/-- Every actual marked side point has a holomorphic reflection coordinate whose upper half is precisely the marked triangle interior locally, and whose closed upper half is the closed triangle locally. -/
theorem MarkedIdealDiskTriangle.exists_oriented_side_coordinate
    (T : MarkedIdealDiskTriangle) (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    {x : ℂ} (hx : x ∈ T.openSide i j) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, x ∈ e.source ∧
      e.source ⊆ {z : ℂ | ‖z‖ < 1} ∧
      DifferentiableOn ℂ e e.source ∧ DifferentiableOn ℂ e.symm e.target ∧
      (e x).im = 0 ∧
      (∀ z ∈ e.source, idealDiskSideReflection (T.vertex i) (T.vertex j) z ∈ e.source) ∧
      (∀ w ∈ e.target, conj w ∈ e.target) ∧
      (∀ z ∈ e.source, e (idealDiskSideReflection (T.vertex i) (T.vertex j) z) = conj (e z)) ∧
      (∀ z ∈ e.source, z ∈ T.interiorSet ↔ 0 < (e z).im) ∧
      ∀ z ∈ e.source, z ∈ T.closedSet ↔ 0 ≤ (e z).im := by
  classical
  let B := T.affineBasis
  let N := {z : ℂ | 0 < B.coord i (idealDiskKlein z) ∧ 0 < B.coord j (idealDiskKlein z)}
  have hN : IsOpen N :=
    (isOpen_lt continuous_const ((continuous_barycentric_coord B i).comp continuous_idealDiskKlein)).inter
      (isOpen_lt continuous_const ((continuous_barycentric_coord B j).comp continuous_idealDiskKlein))
  have hxN : x ∈ N := by
    refine ⟨T.openSide_left_coord_pos i j hij hx, T.openSide_left_coord_pos j i hij.symm ?_⟩
    exact ⟨hx.1, by simpa only [openSegment_symm] using hx.2⟩
  let r := idealDiskSideReflectionPartial (T.vertex i) (T.vertex j)
    (T.norm_vertex i) (T.norm_vertex j) (T.distinct.ne hij)
  have hrfix : r x = x := IdealDiskTriangle.idealDiskSideReflection_fixed_openSide
    (T.norm_vertex i) (T.norm_vertex j) (T.distinct.ne hij)
    ((T.openSide_eq_native i j hij) ▸ hx)
  have hrinv : ∀ z ∈ r.source, r (r z) = z :=
    IdealDiskTriangle.idealDiskSideReflection_involutive_disk_g6
      (T.norm_vertex i) (T.norm_vertex j) (T.distinct.ne hij)
  have hrhol : DifferentiableOn ℂ (fun z ↦ conj (r z)) r.source := by
    intro z hz
    exact (idealDiskSideReflection_conj_differentiableAt
      (T.norm_vertex i) (T.norm_vertex j) hz).differentiableWithinAt
  obtain ⟨e, ε, hε, het, hxe, hsD, hsN, hehol, heinv, hxreal, hrs, hct, hec, haxis⟩ :=
    exists_reflective_holomorphic_ball_coordinate r rfl hrinv hrhol hx.1 hrfix N hN hxN
  let f : ℂ → ℝ := fun w ↦ B.coord k (idealDiskKlein (e.symm w))
  have hf : ContinuousOn f e.target :=
    ((continuous_barycentric_coord B k).comp continuous_idealDiskKlein).comp_continuousOn
      e.symm.continuousOn
  have hzero (w : ℂ) (hw : w ∈ e.target) : f w = 0 ↔ w.im = 0 := by
    have hs := e.map_target hw
    change B.coord k (idealDiskKlein (e.symm w)) = 0 ↔ _
    rw [klein_coord_zero_iff_sideEquation B i j k hij hjk hki
      (T.norm_vertex i) (T.norm_vertex j)]
    change IdealDiskTriangle.sideEquation (T.vertex i) (T.vertex j) (e.symm w) = 0 ↔ w.im = 0
    rw [← idealDiskSideReflection_fixed_iff_sideEquation
      (T.norm_vertex i) (T.norm_vertex j) (T.distinct.ne hij) (hsD hs)]
    have hh := (haxis (e.symm w) hs).symm
    change idealDiskSideReflection (T.vertex i) (T.vertex j) (e.symm w) = e.symm w ↔
      (e (e.symm w)).im = 0 at hh
    simpa only [e.right_inv hw] using hh
  have hflip (w : ℂ) (hw : w ∈ e.target) : 0 ≤ f (conj w) ↔ f w ≤ 0 := by
    have hs := e.map_target hw
    dsimp only [f]
    rw [reflective_coordinate_inverse e r hrs hct hec hw]
    exact klein_coord_reflection_sign B i j k hij hjk hki
      (T.norm_vertex i) (T.norm_vertex j) (T.norm_vertex k) (hsD hs)
  have hconn : IsPreconnected (e.target ∩ {w : ℂ | 0 < w.im}) := by
    rw [het]
    exact ((convex_ball (e x) ε).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hval (z : ℂ) (hz : z ∈ e.source) : f (e z) = B.coord k (idealDiskKlein z) := by
    simp only [f, e.left_inv hz]
  have haxis' (z : ℂ) (hz : z ∈ e.source) :
      B.coord k (idealDiskKlein z) = 0 ↔ (e z).im = 0 := by
    simpa only [hval z hz] using hzero (e z) (e.map_source hz)
  have hInt (z : ℂ) (hz : z ∈ e.source) :
      z ∈ T.interiorSet ↔ 0 < B.coord k (idealDiskKlein z) :=
    T.interiorSet_iff_coord i j k hij hjk hki (hsD hz) (hsN hz).1 (hsN hz).2
  have hClosed (z : ℂ) (hz : z ∈ e.source) :
      z ∈ T.closedSet ↔ 0 ≤ B.coord k (idealDiskKlein z) :=
    T.closedSet_iff_coord i j k hij hjk hki (hsD hz) (hsN hz).1 (hsN hz).2
  have nonneg_iff {a b : ℝ} (hp : 0 < a ↔ 0 < b) (hz : a = 0 ↔ b = 0) :
      0 ≤ a ↔ 0 ≤ b := by
    rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
    exact or_congr hp (by simpa only [eq_comm] using hz)
  rcases reflected_defining_function_orientation e.target hct hconn f hf hzero hflip with hp | hn
  · have hpos (z : ℂ) (hz : z ∈ e.source) :
        0 < B.coord k (idealDiskKlein z) ↔ 0 < (e z).im := by
      simpa only [hval z hz] using hp (e z) (e.map_source hz)
    exact ⟨e, hxe, hsD, hehol, heinv, hxreal, hrs, hct, hec,
      fun z hz ↦ (hInt z hz).trans (hpos z hz),
      fun z hz ↦ (hClosed z hz).trans (nonneg_iff (hpos z hz) (haxis' z hz))⟩
  · let d := e.transHomeomorph (Homeomorph.neg ℂ)
    have hds : d.source = e.source := rfl
    have hdfun (z : ℂ) : d z = -e z := rfl
    have hdhol : DifferentiableOn ℂ d d.source := hehol.neg
    have hdinv : DifferentiableOn ℂ d.symm d.target := by
      intro w hw
      exact (Analysis.Complex.coordinateInverseDeriv d hdhol hw).2.differentiableAt.differentiableWithinAt
    have hdct (w : ℂ) (hw : w ∈ d.target) : conj w ∈ d.target := by
      change -w ∈ e.target at hw
      change -(conj w) ∈ e.target
      simpa only [map_neg] using hct (-w) hw
    have hdc (z : ℂ) (hz : z ∈ d.source) : d (r z) = conj (d z) := by
      simp only [hdfun, hec z hz, map_neg]
    have hdpos (z : ℂ) (hz : z ∈ d.source) :
        0 < B.coord k (idealDiskKlein z) ↔ 0 < (d z).im := by
      simpa only [hval z hz, hdfun, Complex.neg_im, neg_pos] using hn (e z) (e.map_source hz)
    have hdaxis (z : ℂ) (hz : z ∈ d.source) :
        B.coord k (idealDiskKlein z) = 0 ↔ (d z).im = 0 := by
      simpa only [hdfun, Complex.neg_im, neg_eq_zero] using haxis' z hz
    refine ⟨d, hxe, hsD, hdhol, hdinv, ?_, hrs, hdct, hdc,
      fun z hz ↦ (hInt z hz).trans (hdpos z hz),
      fun z hz ↦ (hClosed z hz).trans (nonneg_iff (hdpos z hz) (hdaxis z hz))⟩
    simp only [hdfun, Complex.neg_im, hxreal, neg_zero]

end HolomorphicAnosov

/-! Boundary values of a half-plane chart. (Lyubich, §2.4.13) -/

namespace HolomorphicAnosov
open Filter Set
open scoped _root_.Topology

/-- When a continuous sphere extension takes a finite value at a closure point, the original chart converges to that complex value. -/
theorem chart_tendsto_of_sphere_extension
    (F : OpenPartialHomeomorph ℂ ℂ) (b : ℂ → OnePoint ℂ)
    (hb : ContinuousOn b (closure F.source))
    (heq : EqOn b (fun z ↦ (F z : OnePoint ℂ)) F.source)
    {z w : ℂ} (hz : z ∈ closure F.source) (hw : b z = (w : OnePoint ℂ)) :
    Tendsto F (𝓝[F.source] z) (𝓝 w) := by
  apply OnePoint.isOpenEmbedding_coe.tendsto_nhds_iff.mpr
  have hlim : Tendsto b (𝓝[F.source] z) (𝓝 (b z)) :=
    (hb z hz).mono subset_closure
  rw [hw] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact heq hx

/-- A continuous extension of a partial homeomorphism cannot send a frontier point to its open target. -/
theorem chart_sphere_extension_frontier_not_mem_target
    (F : OpenPartialHomeomorph ℂ ℂ) (b : ℂ → OnePoint ℂ)
    (hb : ContinuousOn b (closure F.source))
    (heq : EqOn b (fun z ↦ (F z : OnePoint ℂ)) F.source)
    {z w : ℂ} (hz : z ∈ frontier F.source) (hw : b z = (w : OnePoint ℂ)) :
    w ∉ F.target := by
  intro hwt
  have hzc : z ∈ closure F.source := frontier_subset_closure hz
  have : (𝓝[F.source] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hzc
  have hlim := chart_tendsto_of_sphere_extension F b hb heq hzc hw
  have hinv := (F.symm.continuousOn.continuousAt (F.open_target.mem_nhds hwt)).tendsto.comp hlim
  have hid : Tendsto (fun x : ℂ ↦ x) (𝓝[F.source] z) (𝓝 (F.symm w)) := by
    apply hinv.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact F.left_inv hx
  have hzeq : z = F.symm w := tendsto_nhds_unique continuousWithinAt_id hid
  have hzs : z ∈ F.source := hzeq ▸ F.map_target hwt
  exact (F.open_source.frontier_eq ▸ hz).2 hzs

/-- Every finite boundary value of a chart onto the upper half-plane is real. (Lyubich, §2.4.13) -/
theorem chart_sphere_extension_frontier_real
    (F : OpenPartialHomeomorph ℂ ℂ) (hF : F.target = {w : ℂ | 0 < w.im})
    (b : ℂ → OnePoint ℂ) (hb : ContinuousOn b (closure F.source))
    (heq : EqOn b (fun z ↦ (F z : OnePoint ℂ)) F.source)
    {z w : ℂ} (hz : z ∈ frontier F.source) (hw : b z = (w : OnePoint ℂ)) :
    w.im = 0 := by
  have hzc : z ∈ closure F.source := frontier_subset_closure hz
  have : (𝓝[F.source] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hzc
  have hlim := chart_tendsto_of_sphere_extension F b hb heq hzc hw
  have hnonneg : 0 ≤ w.im := by
    apply isClosed_Ici.mem_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp hlim)
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hFx := F.map_source hx
    rw [hF] at hFx
    exact le_of_lt (show 0 < (F x).im from hFx)
  have hnot := chart_sphere_extension_frontier_not_mem_target F b hb heq hz hw
  rw [hF] at hnot
  exact le_antisymm (le_of_not_gt hnot) hnonneg

/-- Read the finite complex value of a sphere-valued map, with a harmless zero fallback at infinity. -/
def sphereFiniteValue (b : ℂ → OnePoint ℂ) (z : ℂ) : ℂ := (b z).elim 0 id

/-- On the finite-value locus this operation is the inverse complex inclusion. -/
theorem sphereFiniteValue_coe (b : ℂ → OnePoint ℂ) {z : ℂ}
    (hz : b z ≠ OnePoint.infty) : (sphereFiniteValue b z : OnePoint ℂ) = b z := by
  obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hz
  unfold sphereFiniteValue
  rw [← hw]
  rfl

/-- A continuous sphere map with finite values on a set is continuous as a complex map there, because the complex inclusion is a topological embedding. -/
theorem sphereFiniteValue_continuousOn (b : ℂ → OnePoint ℂ) {C : Set ℂ}
    (hb : ContinuousOn b C) (hfinite : ∀ z ∈ C, b z ≠ OnePoint.infty) :
    ContinuousOn (sphereFiniteValue b) C := by
  apply OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff.mpr
  exact hb.congr (fun z hz ↦ sphereFiniteValue_coe b (hfinite z hz))

/-- Injectivity of the sphere extension passes to its finite complex values. -/
theorem sphereFiniteValue_injOn (b : ℂ → OnePoint ℂ) {C : Set ℂ}
    (hb : InjOn b C) (hfinite : ∀ z ∈ C, b z ≠ OnePoint.infty) :
    InjOn (sphereFiniteValue b) C := by
  intro x hx y hy he
  apply hb hx hy
  rw [← sphereFiniteValue_coe b (hfinite x hx), ← sphereFiniteValue_coe b (hfinite y hy), he]

/-- Agreement with a finite chart is preserved when taking complex values. -/
theorem sphereFiniteValue_eqOn (b : ℂ → OnePoint ℂ) (f : ℂ → ℂ) {C : Set ℂ}
    (hb : EqOn b (fun z ↦ (f z : OnePoint ℂ)) C) : EqOn (sphereFiniteValue b) f C := by
  intro z hz
  unfold sphereFiniteValue
  rw [hb hz]
  rfl

end HolomorphicAnosov

/-! Biholomorphic charts obtained by Schwarz reflection. (Bullett, Prop. 23.1; Lyubich, §2.4.13) -/

noncomputable section
namespace HolomorphicAnosov
open Set Filter Complex
open scoped _root_.Topology ComplexConjugate

/-- A holomorphic function injective on an open set is open on that set. -/
theorem holomorphic_injective_isOpenMap {U : Set ℂ} (hU : IsOpen U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) :
    IsOpenMap (fun z : U ↦ f z.val) := by
  rw [isOpenMap_iff_nhds_le]
  intro z
  rcases (hf.analyticOnNhd hU z.val z.property).eventually_constant_or_nhds_le_map_nhds with hc | ho
  · have hs : ({z.val} : Set ℂ) ∈ 𝓝 z.val := by
      filter_upwards [hc, hU.mem_nhds z.property] with w hw hwU
      exact hi hwU z.property hw
    exact (not_isOpen_singleton z.val
      (isOpen_singleton_of_finite_mem_nhds _ hs (Set.finite_singleton _))).elim
  · change 𝓝 (f z.val) ≤ Filter.map (f ∘ Subtype.val) (𝓝 z)
    rw [← Filter.map_map, hU.isOpenEmbedding_subtypeVal.map_nhds_eq]
    exact ho

/-- Package an injective holomorphic function on an open set as its literal partial homeomorphism onto its image. -/
def holomorphicInjectivePartial (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) : OpenPartialHomeomorph ℂ ℂ :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict (hi.toPartialEquiv f U)
    hf.continuousOn (holomorphic_injective_isOpenMap hU f hf hi) hU

/-- The inverse of the injective holomorphic chart is holomorphic on its literal target, by the existing one-variable inverse-derivative theorem. -/
theorem holomorphicInjectivePartial_symm (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) :
    DifferentiableOn ℂ (holomorphicInjectivePartial f U hU hf hi).symm
      (holomorphicInjectivePartial f U hU hf hi).target := by
  intro w hw
  exact (Analysis.Complex.coordinateInverseDeriv
    (holomorphicInjectivePartial f U hU hf hi) hf hw).2.differentiableAt.differentiableWithinAt

/-- Reflection of an injective upper-half chart with positive imaginary interior values is injective on the entire symmetric open set. -/
theorem schwarz_real_boundary_extension_injective {U : Set ℂ}
    (hU : IsOpen U) (hconj : ∀ z ∈ U, conj z ∈ U)
    (f : {z : ℂ // z ∈ U ∧ 0 ≤ z.im} → ℂ)
    (hf_cont : Continuous f)
    (hf_holo : DifferentiableOn ℂ (Function.extend Subtype.val f (fun _ ↦ 0))
      {z : ℂ | z ∈ U ∧ 0 < z.im})
    (hf_real : ∀ z : {z : ℂ // z ∈ U ∧ 0 ≤ z.im}, z.val.im = 0 → (f z).im = 0)
    (hf_pos : ∀ z : {z : ℂ // z ∈ U ∧ 0 ≤ z.im}, 0 < z.val.im → 0 < (f z).im)
    (hf_inj : Function.Injective f) :
    Function.Injective (schwarzRealBoundaryExtension hconj f) := by
  let F := schwarzRealBoundaryExtension hconj f
  obtain ⟨_, _, hu, hc⟩ := schwarz_real_boundary_extension hU hconj f hf_cont hf_holo hf_real
  have hnonneg (z : U) (hz : 0 ≤ z.val.im) : 0 ≤ (F z).im := by
    rw [show F z = f ⟨z.val, z.property, hz⟩ from hu ⟨z.val, z.property, hz⟩]
    rcases hz.eq_or_lt with he | hp
    · rw [hf_real _ he.symm]
    · exact (hf_pos _ hp).le
  have hneg (z : U) (hz : z.val.im < 0) : (F z).im < 0 := by
    let cz : U := ⟨conj z.val, hconj z.val z.property⟩
    have hcz : 0 < cz.val.im := by simpa only [cz, Complex.conj_im] using neg_pos.mpr hz
    have hp : 0 < (F cz).im := by
      rw [show F cz = f ⟨cz.val, cz.property, hcz.le⟩ from hu ⟨cz.val, cz.property, hcz.le⟩]
      exact hf_pos _ hcz
    have he : F cz = conj (F z) := hc z
    rw [he, Complex.conj_im] at hp
    linarith
  have hupper (x y : U) (hx : 0 ≤ x.val.im) (hy : 0 ≤ y.val.im)
      (he : F x = F y) : x = y := by
    have he' : f ⟨x.val, x.property, hx⟩ = f ⟨y.val, y.property, hy⟩ :=
      (hu ⟨x.val, x.property, hx⟩).symm.trans (he.trans (hu ⟨y.val, y.property, hy⟩))
    exact Subtype.ext (congrArg (fun z : {z : ℂ // z ∈ U ∧ 0 ≤ z.im} ↦ z.val) (hf_inj he'))
  intro x y he
  change F x = F y at he
  by_cases hx : 0 ≤ x.val.im
  · by_cases hy : 0 ≤ y.val.im
    · exact hupper x y hx hy he
    · have hxp := hnonneg x hx
      have hyn := hneg y (lt_of_not_ge hy)
      rw [he] at hxp
      linarith
  · by_cases hy : 0 ≤ y.val.im
    · have hxn := hneg x (lt_of_not_ge hx)
      have hyp := hnonneg y hy
      rw [he] at hxn
      linarith
    · let cx : U := ⟨conj x.val, hconj x.val x.property⟩
      let cy : U := ⟨conj y.val, hconj y.val y.property⟩
      have hcx : 0 ≤ cx.val.im := by simp only [cx, Complex.conj_im]; linarith
      have hcy : 0 ≤ cy.val.im := by simp only [cy, Complex.conj_im]; linarith
      have hec : F cx = F cy := (hc x).trans ((congrArg conj he).trans (hc y).symm)
      have hexy := congrArg (fun z : U ↦ conj z.val) (hupper cx cy hcx hcy hec)
      exact Subtype.ext (by simpa only [cx, cy, Complex.conj_conj] using hexy)

/-- Schwarz reflection of an injective upper-half chart produces a literal biholomorphic partial homeomorphism on the whole symmetric open set. -/
theorem exists_schwarz_biholomorphic_chart {U : Set ℂ}
    (hU : IsOpen U) (hconj : ∀ z ∈ U, conj z ∈ U)
    (f : {z : ℂ // z ∈ U ∧ 0 ≤ z.im} → ℂ)
    (hf_cont : Continuous f)
    (hf_holo : DifferentiableOn ℂ (Function.extend Subtype.val f (fun _ ↦ 0))
      {z : ℂ | z ∈ U ∧ 0 < z.im})
    (hf_real : ∀ z : {z : ℂ // z ∈ U ∧ 0 ≤ z.im}, z.val.im = 0 → (f z).im = 0)
    (hf_pos : ∀ z : {z : ℂ // z ∈ U ∧ 0 ≤ z.im}, 0 < z.val.im → 0 < (f z).im)
    (hf_inj : Function.Injective f) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, e.source = U ∧
      DifferentiableOn ℂ e e.source ∧ DifferentiableOn ℂ e.symm e.target ∧
      (∀ z : {z : ℂ // z ∈ U ∧ 0 ≤ z.im}, e z.val = f z) ∧
      ∀ z ∈ U, e (conj z) = conj (e z) := by
  let F := schwarzRealBoundaryExtension hconj f
  let G : ℂ → ℂ := Function.extend Subtype.val F (fun _ ↦ 0)
  obtain ⟨hG, _, hu, hc⟩ := schwarz_real_boundary_extension hU hconj f hf_cont hf_holo hf_real
  have hval (z : U) : G z.val = F z := Subtype.val_injective.extend_apply _ _ z
  have hFinj := schwarz_real_boundary_extension_injective hU hconj f
    hf_cont hf_holo hf_real hf_pos hf_inj
  have hGinj : InjOn G U := by
    intro x hx y hy he
    have heF : F ⟨x, hx⟩ = F ⟨y, hy⟩ :=
      (hval ⟨x, hx⟩).symm.trans (he.trans (hval ⟨y, hy⟩))
    exact congrArg (fun z : U ↦ z.val) (hFinj heF)
  let e := holomorphicInjectivePartial G U hU hG hGinj
  refine ⟨e, rfl, hG, holomorphicInjectivePartial_symm G U hU hG hGinj, ?_, ?_⟩
  · intro z
    exact (hval ⟨z.val, z.property.1⟩).trans (hu z)
  · intro z hz
    exact (hval ⟨conj z, hconj z hz⟩).trans
      ((hc ⟨z, hz⟩).trans (congrArg conj (hval ⟨z, hz⟩).symm))

/-- A holomorphic coordinate which flattens an analytic side transports Schwarz reflection back to a literal biholomorphic chart across that side. -/
theorem exists_biholomorphic_chart_across_flattened_side
    (F e : OpenPartialHomeomorph ℂ ℂ)
    (hFt : F.target = {w : ℂ | 0 < w.im})
    (hFhol : DifferentiableOn ℂ F F.source)
    (hehol : DifferentiableOn ℂ e e.source)
    (heinv : DifferentiableOn ℂ e.symm e.target)
    (heconj : ∀ w ∈ e.target, conj w ∈ e.target)
    (hpos : ∀ z ∈ e.source, z ∈ F.source ↔ 0 < (e z).im)
    (C : Set ℂ) (b : ℂ → ℂ) (hbcont : ContinuousOn b C)
    (hbinj : InjOn b C) (hbeq : EqOn b F F.source)
    (hclosed : ∀ w ∈ e.target, 0 ≤ w.im → e.symm w ∈ C)
    (hreal : ∀ w ∈ e.target, w.im = 0 → (b (e.symm w)).im = 0)
    (r : ℂ → ℂ)
    (hequiv : ∀ z ∈ e.source, e (r z) = conj (e z)) :
    ∃ H : OpenPartialHomeomorph ℂ ℂ, H.source = e.source ∧
      DifferentiableOn ℂ H H.source ∧ DifferentiableOn ℂ H.symm H.target ∧
      EqOn H F (e.source ∩ F.source) ∧
      (∀ z ∈ e.source, 0 ≤ (e z).im → H z = b z) ∧
      ∀ z ∈ e.source, H (r z) = conj (H z) := by
  let f : {w : ℂ // w ∈ e.target ∧ 0 ≤ w.im} → ℂ := fun w ↦ b (e.symm w.val)
  have hmap {w : ℂ} (hw : w ∈ e.target) (hwi : 0 < w.im) : e.symm w ∈ F.source := by
    apply (hpos _ (e.map_target hw)).mpr
    simpa only [e.right_inv hw] using hwi
  have hfcont : Continuous f := by
    have hi : Continuous (fun w : {w : ℂ // w ∈ e.target ∧ 0 ≤ w.im} ↦ e.symm w.val) :=
      e.symm.continuousOn.comp_continuous continuous_subtype_val (fun w ↦ w.property.1)
    exact hbcont.comp_continuous hi (fun w ↦ hclosed w.val w.property.1 w.property.2)
  have hfhol : DifferentiableOn ℂ (Function.extend Subtype.val f (fun _ ↦ 0))
      {w : ℂ | w ∈ e.target ∧ 0 < w.im} := by
    have hh := hFhol.comp (heinv.mono (show {w : ℂ | w ∈ e.target ∧ 0 < w.im} ⊆ e.target
      from fun _ hw ↦ hw.1)) (fun w hw ↦ hmap hw.1 hw.2)
    apply hh.congr
    intro w hw
    have hv := Subtype.val_injective.extend_apply f (fun _ ↦ (0 : ℂ))
      ⟨w, hw.1, hw.2.le⟩
    rw [hv]
    exact hbeq (hmap hw.1 hw.2)
  have hfreal (w : {w : ℂ // w ∈ e.target ∧ 0 ≤ w.im}) (hw : w.val.im = 0) :
      (f w).im = 0 := hreal w.val w.property.1 hw
  have hfpos (w : {w : ℂ // w ∈ e.target ∧ 0 ≤ w.im}) (hw : 0 < w.val.im) :
      0 < (f w).im := by
    change 0 < (b (e.symm w.val)).im
    rw [hbeq (hmap w.property.1 hw)]
    have hm := F.map_source (hmap w.property.1 hw)
    rwa [hFt] at hm
  have hfinj : Function.Injective f := by
    intro w v heq
    have he := hbinj (hclosed w.val w.property.1 w.property.2)
      (hclosed v.val v.property.1 v.property.2) heq
    exact Subtype.ext (e.symm.injOn w.property.1 v.property.1 he)
  obtain ⟨k, hks, hkhol, _, hkupper, hkconj⟩ := exists_schwarz_biholomorphic_chart
    e.open_target heconj f hfcont hfhol hfreal hfpos hfinj
  let H := e.trans k
  have hHs : H.source = e.source := by
    rw [OpenPartialHomeomorph.trans_source, hks]
    exact Set.inter_eq_left.mpr (fun z hz ↦ e.map_source hz)
  have hHhol : DifferentiableOn ℂ H H.source := by
    change DifferentiableOn ℂ (k ∘ e) H.source
    rw [hHs]
    exact hkhol.comp hehol (fun z hz ↦ hks.symm ▸ e.map_source hz)
  have hHinv : DifferentiableOn ℂ H.symm H.target := by
    intro w hw
    exact (Analysis.Complex.coordinateInverseDeriv H hHhol hw).2.differentiableAt.differentiableWithinAt
  have hHupper (z : ℂ) (hz : z ∈ e.source) (hzi : 0 ≤ (e z).im) : H z = b z := by
    have he := hkupper ⟨e z, e.map_source hz, hzi⟩
    change k (e z) = b (e.symm (e z)) at he
    change k (e z) = b z
    simpa only [e.left_inv hz] using he
  refine ⟨H, hHs, hHhol, hHinv, ?_, hHupper, ?_⟩
  · intro z hz
    exact (hHupper z hz.1 ((hpos z hz.1).mp hz.2).le).trans (hbeq hz.2)
  · intro z hz
    change k (e (r z)) = conj (k (e z))
    rw [hequiv z hz]
    exact hkconj (e z) (e.map_source hz)

end HolomorphicAnosov
namespace HolomorphicAnosov
open Set
open scoped ComplexConjugate _root_.Topology

/-- Schwarz reflection gives a literal biholomorphic chart near any open side point of a marked ideal triangle. (Lyubich, §2.4.13) -/
theorem MarkedIdealDiskTriangle.exists_side_extension
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hFs : F.source = T.interiorSet) (hFt : F.target = {w : ℂ | 0 < w.im})
    (hFhol : DifferentiableOn ℂ F F.source)
    (hclosure : closure T.interiorSet = T.closedSet)
    (b : ℂ → OnePoint ℂ) (hbcont : ContinuousOn b T.closedSet)
    (hbinj : InjOn b T.closedSet)
    (hbeq : EqOn b (fun z ↦ (F z : OnePoint ℂ)) T.interiorSet)
    (hb0 : b (T.vertex 0) = ((0 : ℂ) : OnePoint ℂ))
    (hb1 : b (T.vertex 1) = ((1 : ℂ) : OnePoint ℂ))
    (hb2 : b (T.vertex 2) = OnePoint.infty)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    {x : ℂ} (hx : x ∈ T.openSide i j) :
    ∃ H : OpenPartialHomeomorph ℂ ℂ, x ∈ H.source ∧
      H.source ⊆ {z : ℂ | ‖z‖ < 1} ∧
      H.source ⊆ T.interiorSet ∪ T.openSide i j ∪
        idealDiskSideReflection (T.vertex i) (T.vertex j) '' T.interiorSet ∧
      DifferentiableOn ℂ H H.source ∧ DifferentiableOn ℂ H.symm H.target ∧
      EqOn H F (H.source ∩ T.interiorSet) ∧
      (∀ z ∈ H.source ∩ T.closedSet, (H z : OnePoint ℂ) = b z) ∧
      (∀ z ∈ H.source, idealDiskSideReflection (T.vertex i) (T.vertex j) z ∈ H.source) ∧
      ∀ z ∈ H.source, H (idealDiskSideReflection (T.vertex i) (T.vertex j) z) = conj (H z) := by
  obtain ⟨e, hxe, hsD, hehol, heinv, _, hrs, heconj, hequiv, hpos, hclosed⟩ :=
    T.exists_oriented_side_coordinate i j k hij hjk hki hx
  let C := T.closedSet ∩ {z : ℂ | ‖z‖ < 1}
  have hfinite (z : ℂ) (hz : z ∈ C) : b z ≠ OnePoint.infty := by
    obtain ⟨w, hw, _, _⟩ := T.sphere_extension_disk_value b hbinj hb0 hb1 hb2 hz.1 hz.2
    rw [hw]
    exact OnePoint.coe_ne_infty w
  have hBcont : ContinuousOn (sphereFiniteValue b) C :=
    sphereFiniteValue_continuousOn b (hbcont.mono inter_subset_left) hfinite
  have hBinj : InjOn (sphereFiniteValue b) C :=
    sphereFiniteValue_injOn b (hbinj.mono inter_subset_left) hfinite
  have hBeq : EqOn (sphereFiniteValue b) F F.source := by
    rw [hFs]
    exact sphereFiniteValue_eqOn b F hbeq
  have hEpos (z : ℂ) (hz : z ∈ e.source) : z ∈ F.source ↔ 0 < (e z).im := by
    rw [hFs]
    exact hpos z hz
  have hEclosed (w : ℂ) (hw : w ∈ e.target) (hwi : 0 ≤ w.im) : e.symm w ∈ C := by
    refine ⟨(hclosed _ (e.map_target hw)).mpr ?_, hsD (e.map_target hw)⟩
    simpa only [e.right_inv hw] using hwi
  have hEreal (w : ℂ) (hw : w ∈ e.target) (hwi : w.im = 0) :
      (sphereFiniteValue b (e.symm w)).im = 0 := by
    have hzC := hEclosed w hw hwi.ge
    have hzfront : e.symm w ∈ frontier F.source := by
      rw [F.open_source.frontier_eq, hFs, hclosure]
      refine ⟨hzC.1, ?_⟩
      intro hz
      have hh := (hpos _ (e.map_target hw)).mp hz
      simp only [e.right_inv hw, hwi, lt_self_iff_false] at hh
    apply chart_sphere_extension_frontier_real F hFt b
      (by simpa only [hFs, hclosure] using hbcont)
      (by simpa only [hFs] using hbeq) hzfront
    exact (sphereFiniteValue_coe b (hfinite _ hzC)).symm
  obtain ⟨H, hHs, hHhol, hHinv, hHeq, hHupper, hHconj⟩ :=
    exists_biholomorphic_chart_across_flattened_side F e hFt hFhol hehol heinv heconj
      hEpos C (sphereFiniteValue b) hBcont hBinj hBeq hEclosed hEreal
      (idealDiskSideReflection (T.vertex i) (T.vertex j)) hequiv
  have hpair : e.source ⊆ T.interiorSet ∪ T.openSide i j ∪
      idealDiskSideReflection (T.vertex i) (T.vertex j) '' T.interiorSet := by
    intro z hz
    rcases lt_trichotomy 0 (e z).im with hp | he | hn
    · exact Or.inl (Or.inl ((hpos z hz).mpr hp))
    · have hfix : idealDiskSideReflection (T.vertex i) (T.vertex j) z = z :=
        e.injOn (hrs z hz) hz (by
          rw [hequiv z hz]
          exact Complex.conj_eq_iff_im.mpr he.symm)
      have heq := (idealDiskSideReflection_fixed_iff_sideEquation
        (T.norm_vertex i) (T.norm_vertex j) (T.distinct.ne hij) (hsD hz)).mp hfix
      apply Or.inl ∘ Or.inr
      rw [T.openSide_eq_native i j hij]
      exact ⟨hsD hz, heq⟩
    · have hrint : idealDiskSideReflection (T.vertex i) (T.vertex j) z ∈ T.interiorSet := by
        apply (hpos _ (hrs z hz)).mpr
        rw [hequiv z hz, Complex.conj_im]
        exact neg_pos.mpr hn
      exact Or.inr ⟨_, hrint, IdealDiskTriangle.idealDiskSideReflection_involutive_disk_g6
        (T.norm_vertex i) (T.norm_vertex j) (T.distinct.ne hij) z (hsD hz)⟩
  refine ⟨H, hHs.symm ▸ hxe, hHs ▸ hsD, hHs ▸ hpair, hHhol, hHinv, ?_, ?_, ?_, ?_⟩
  · simpa only [hHs, hFs] using hHeq
  · intro z hz
    have hze : z ∈ e.source := hHs ▸ hz.1
    rw [hHupper z hze ((hclosed z hze).mp hz.2)]
    exact sphereFiniteValue_coe b (hfinite z ⟨hz.2, hsD hze⟩)
  · simpa only [hHs] using hrs
  · simpa only [hHs] using hHconj

end HolomorphicAnosov
namespace HolomorphicAnosov
open scoped ComplexConjugate
/-- Reflect a complex chart in a geometric source side and conjugate its values. (Lyubich, §2.4.13) -/
noncomputable def idealDiskReflectedChart (p q : ℂ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q)
    (F : OpenPartialHomeomorph ℂ ℂ) : OpenPartialHomeomorph ℂ ℂ :=
  ((idealDiskSideReflectionPartial p q hp hq hpq).trans F).transHomeomorph
    Complex.conjCLE.toHomeomorph

/-- On the reflected chart source the forward formula is holomorphic, by the conjugation-sandwich chain rule and holomorphy of the original chart. -/
theorem idealDiskReflectedChart_differentiableOn (p q : ℂ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q)
    (F : OpenPartialHomeomorph ℂ ℂ) (hF : DifferentiableOn ℂ F F.source) :
    DifferentiableOn ℂ (idealDiskReflectedChart p q hp hq hpq F)
      (idealDiskReflectedChart p q hp hq hpq F).source := by
  intro z hz
  change ‖z‖ < 1 ∧ idealDiskSideReflection p q z ∈ F.source at hz
  exact (idealDiskSideReflection_conj_comp_differentiableAt hp hq hz.1
    (hF.differentiableAt (F.open_source.mem_nhds hz.2))).differentiableWithinAt

/-- If the initial chart lies in the disk and has a holomorphic inverse, the reflected chart also has a holomorphic inverse. -/
theorem idealDiskReflectedChart_symm_differentiableOn (p q : ℂ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q)
    (F : OpenPartialHomeomorph ℂ ℂ)
    (hFsource : F.source ⊆ {z : ℂ | ‖z‖ < 1})
    (hF : DifferentiableOn ℂ F.symm F.target) :
    DifferentiableOn ℂ (idealDiskReflectedChart p q hp hq hpq F).symm
      (idealDiskReflectedChart p q hp hq hpq F).target := by
  intro z hz
  change conj z ∈ F.target ∧ F.symm (conj z) ∈
    (idealDiskSideReflectionPartial p q hp hq hpq).target at hz
  exact (idealDiskSideReflection_comp_conj_differentiableAt hp hq
    (hFsource (F.map_target hz.1))
    (hF.differentiableAt (F.open_target.mem_nhds hz.1))).differentiableWithinAt

/-- The reflected chart has exactly the reflected source. -/
theorem idealDiskReflectedChart_source (p q : ℂ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q)
    (F : OpenPartialHomeomorph ℂ ℂ)
    (hFsource : F.source ⊆ {z : ℂ | ‖z‖ < 1}) :
    (idealDiskReflectedChart p q hp hq hpq F).source =
      idealDiskSideReflection p q '' F.source := by
  ext z
  change (‖z‖ < 1 ∧ idealDiskSideReflection p q z ∈ F.source) ↔ _
  constructor
  · intro hz
    exact ⟨_, hz.2,
      IdealDiskTriangle.idealDiskSideReflection_involutive_disk_g6 hp hq hpq _ hz.1⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨IdealDiskTriangle.idealDiskSideReflection_mem_disk_g6 hp hq hpq (hFsource hx), ?_⟩
    simpa only [IdealDiskTriangle.idealDiskSideReflection_involutive_disk_g6 hp hq hpq
      x (hFsource hx)] using hx

/-- Target conjugation gives precisely the conjugate of the original chart target; the disk restriction loses nothing when the original source lies there. -/
theorem idealDiskReflectedChart_target (p q : ℂ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q)
    (F : OpenPartialHomeomorph ℂ ℂ)
    (hFsource : F.source ⊆ {z : ℂ | ‖z‖ < 1}) :
    (idealDiskReflectedChart p q hp hq hpq F).target = conj '' F.target := by
  ext z
  change (conj z ∈ F.target ∧ ‖F.symm (conj z)‖ < 1) ↔ _
  constructor
  · intro hz
    exact ⟨conj z, hz.1, Complex.conj_conj z⟩
  · rintro ⟨x, hx, rfl⟩
    simpa only [Complex.conj_conj, Set.mem_ofPred_eq] using And.intro hx (hFsource (F.map_target hx))

/-- Evaluation on the geometric reflection of a disk point cancels the two source reflections, leaving exactly one target conjugation. -/
theorem idealDiskReflectedChart_apply_reflection (p q : ℂ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q)
    (F : OpenPartialHomeomorph ℂ ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    idealDiskReflectedChart p q hp hq hpq F (idealDiskSideReflection p q z) =
      conj (F z) := by
  change conj (F (idealDiskSideReflection p q (idealDiskSideReflection p q z))) = _
  rw [IdealDiskTriangle.idealDiskSideReflection_involutive_disk_g6 hp hq hpq z hz]

/-- The fold convention puts the first letter on the outside of an itinerary. -/
theorem MarkedIdealDiskTriangle.itineraryMap_cons (T : MarkedIdealDiskTriangle)
    (i : Fin 3) (w : List (Fin 3)) :
    T.itineraryMap (i :: w) =
      idealDiskSideReflection (T.vertex i) (T.vertex (i + 1)) ∘ T.itineraryMap w := by
  let r (j : Fin 3) := idealDiskSideReflection (T.vertex j) (T.vertex (j + 1))
  have hfold : ∀ (l : List (Fin 3)) (g h : ℂ → ℂ),
      l.foldl (fun k j ↦ k ∘ r j) (g ∘ h) =
        g ∘ l.foldl (fun k j ↦ k ∘ r j) h := by
    intro l
    induction l with
    | nil => intro g h; rfl
    | cons j l ih =>
      intro g h
      change l.foldl (fun k j ↦ k ∘ r j) ((g ∘ h) ∘ r j) =
        g ∘ l.foldl (fun k j ↦ k ∘ r j) (h ∘ r j)
      rw [Function.comp_assoc, ih]
  change w.foldl (fun k j ↦ k ∘ r j) (id ∘ r i) =
    r i ∘ w.foldl (fun k j ↦ k ∘ r j) id
  simpa only [Function.id_comp, Function.comp_id] using hfold w (r i) id

/-- Adjacent cyclic marks are distinct, including the wrap from mark two to zero. -/
theorem MarkedIdealDiskTriangle.vertex_ne_next (T : MarkedIdealDiskTriangle) (i : Fin 3) :
    T.vertex i ≠ T.vertex (i + 1) := by
  apply T.distinct.ne
  intro h
  have hv := congrArg Fin.val h
  omega

/-- The literal reflected chart of a finite itinerary. (Lyubich, §2.4.13) -/
noncomputable def MarkedIdealDiskTriangle.itineraryChart
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ) :
    List (Fin 3) → OpenPartialHomeomorph ℂ ℂ
  | [] => F
  | i :: w => idealDiskReflectedChart (T.vertex i) (T.vertex (i + 1))
      (T.norm_vertex i) (T.norm_vertex (i + 1)) (T.vertex_ne_next i) (T.itineraryChart F w)

/-- The source of each recursively reflected chart remains inside the disk. -/
theorem MarkedIdealDiskTriangle.itineraryChart_source_subset
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hF : F.source ⊆ {z : ℂ | ‖z‖ < 1}) (w : List (Fin 3)) :
    (T.itineraryChart F w).source ⊆ {z : ℂ | ‖z‖ < 1} := by
  cases w with
  | nil => exact hF
  | cons i w => exact fun _ h ↦ h.1

/-- The chart produced by a word has exactly the literal itinerary-image source. -/
theorem MarkedIdealDiskTriangle.itineraryChart_source
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hF : F.source ⊆ {z : ℂ | ‖z‖ < 1}) (w : List (Fin 3)) :
    (T.itineraryChart F w).source = T.itineraryMap w '' F.source := by
  induction w with
  | nil => simp [itineraryChart, itineraryMap]
  | cons i w ih =>
    rw [itineraryChart, idealDiskReflectedChart_source _ _ _ _ _ _
      (T.itineraryChart_source_subset F hF w), ih, itineraryMap_cons, Set.image_comp]

/-- Every reflected tile chart is biholomorphic whenever the original is. -/
theorem MarkedIdealDiskTriangle.itineraryChart_biholomorphic
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hFsource : F.source ⊆ {z : ℂ | ‖z‖ < 1})
    (hF : DifferentiableOn ℂ F F.source) (hFi : DifferentiableOn ℂ F.symm F.target)
    (w : List (Fin 3)) :
    DifferentiableOn ℂ (T.itineraryChart F w) (T.itineraryChart F w).source ∧
      DifferentiableOn ℂ (T.itineraryChart F w).symm (T.itineraryChart F w).target := by
  induction w with
  | nil => exact ⟨hF, hFi⟩
  | cons i w ih =>
    exact ⟨idealDiskReflectedChart_differentiableOn _ _ _ _ _ _ ih.1,
      idealDiskReflectedChart_symm_differentiableOn _ _ _ _ _ _
        (T.itineraryChart_source_subset F hFsource w) ih.2⟩

/-- The reflected chart target is the iterated conjugate of the original target, with one conjugation per itinerary letter. -/
theorem MarkedIdealDiskTriangle.itineraryChart_target
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hF : F.source ⊆ {z : ℂ | ‖z‖ < 1}) (w : List (Fin 3)) :
    (T.itineraryChart F w).target = (conj^[w.length]) '' F.target := by
  induction w with
  | nil => simp [itineraryChart]
  | cons i w ih =>
    rw [itineraryChart, idealDiskReflectedChart_target _ _ _ _ _ _
      (T.itineraryChart_source_subset F hF w), ih, List.length_cons,
      Function.iterate_succ', Set.image_comp]

/-- On its itinerary image, a reflected chart takes the original value conjugated once for every letter. -/
theorem MarkedIdealDiskTriangle.itineraryChart_apply
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hF : F.source ⊆ {z : ℂ | ‖z‖ < 1}) (w : List (Fin 3))
    {z : ℂ} (hz : z ∈ F.source) :
    T.itineraryChart F w (T.itineraryMap w z) = (conj^[w.length]) (F z) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hmem : T.itineraryMap w z ∈ (T.itineraryChart F w).source := by
      rw [T.itineraryChart_source F hF w]
      exact Set.mem_image_of_mem _ hz
    have hnorm := T.itineraryChart_source_subset F hF w hmem
    simp only [itineraryChart, itineraryMap_cons, Function.comp_apply]
    rw [idealDiskReflectedChart_apply_reflection _ _ _ _ _ _ hnorm, ih,
      List.length_cons, Function.iterate_succ_apply']

/-- Concatenating reflection words composes their literal disk maps. -/
theorem MarkedIdealDiskTriangle.itineraryMap_append (T : MarkedIdealDiskTriangle)
    (u v : List (Fin 3)) : T.itineraryMap (u ++ v) = T.itineraryMap u ∘ T.itineraryMap v := by
  induction u with
  | nil => rfl
  | cons i u ih =>
    rw [List.cons_append, itineraryMap_cons, ih, itineraryMap_cons, Function.comp_assoc]

/-- Reversing a reflection word inverts its map on the disk: the two equal reflections at the join cancel and the remaining word is handled inductively. -/
theorem MarkedIdealDiskTriangle.itineraryMap_reverse_apply
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) {z : ℂ} (hz : ‖z‖ < 1) :
    T.itineraryMap w.reverse (T.itineraryMap w z) = z := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [List.reverse_cons, itineraryMap_append, itineraryMap_cons, itineraryMap_cons]
    change T.itineraryMap w.reverse
      (idealDiskSideReflection (T.vertex i) (T.vertex (i + 1))
        (idealDiskSideReflection (T.vertex i) (T.vertex (i + 1))
          (T.itineraryMap w z))) = z
    rw [IdealDiskTriangle.idealDiskSideReflection_involutive_disk_g6
      (T.norm_vertex i) (T.norm_vertex (i + 1)) (T.vertex_ne_next i)
      _ (lyubich_itinerary_map_disk_preserving T w hz)]
    exact ih

/-- Literal reflection itineraries are injective on the open disk because the reversed itinerary is a left inverse there. -/
theorem MarkedIdealDiskTriangle.itineraryMap_injOn (T : MarkedIdealDiskTriangle)
    (w : List (Fin 3)) : Set.InjOn (T.itineraryMap w) {z : ℂ | ‖z‖ < 1} := by
  intro z hz t ht heq
  have h := congrArg (T.itineraryMap w.reverse) heq
  simpa only [T.itineraryMap_reverse_apply w hz, T.itineraryMap_reverse_apply w ht] using h

/-- Deleting an immediate repeated-side backtrack does not change the itinerary map on the disk. -/
theorem MarkedIdealDiskTriangle.itineraryMap_cancel_backtrack
    (T : MarkedIdealDiskTriangle) (u v : List (Fin 3)) (i : Fin 3)
    {z : ℂ} (hz : ‖z‖ < 1) :
    T.itineraryMap (u ++ i :: i :: v) z = T.itineraryMap (u ++ v) z := by
  simp only [itineraryMap_append, itineraryMap_cons, Function.comp_apply]
  rw [IdealDiskTriangle.idealDiskSideReflection_involutive_disk_g6
    (T.norm_vertex i) (T.norm_vertex (i + 1)) (T.vertex_ne_next i)
    _ (lyubich_itinerary_map_disk_preserving T v hz)]

/-- Two itinerary charts with the same source transport and the same conjugation parity agree on that transported source. -/
theorem MarkedIdealDiskTriangle.itineraryChart_eqOn_of_transport_eq
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hF : F.source ⊆ {z : ℂ | ‖z‖ < 1}) (u v : List (Fin 3))
    (hmap : Set.EqOn (T.itineraryMap u) (T.itineraryMap v) F.source)
    (hparity : (conj^[u.length] : ℂ → ℂ) = conj^[v.length]) :
    (T.itineraryChart F u).source = (T.itineraryChart F v).source ∧
      Set.EqOn (T.itineraryChart F u) (T.itineraryChart F v) (T.itineraryChart F u).source := by
  have hs : (T.itineraryChart F u).source = (T.itineraryChart F v).source := by
    rw [T.itineraryChart_source F hF u, T.itineraryChart_source F hF v]
    exact hmap.image_eq
  refine ⟨hs, ?_⟩
  intro z hz
  rw [T.itineraryChart_source F hF u] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [T.itineraryChart_apply F hF u hx, hmap hx, T.itineraryChart_apply F hF v hx, hparity]

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set Filter
open scoped ComplexConjugate _root_.Topology

/-- A side reflection sends the initial triangle interior strictly outside that interior. -/
theorem MarkedIdealDiskTriangle.reflection_interior_disjoint
    (T : MarkedIdealDiskTriangle) (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    Disjoint T.interiorSet
      (idealDiskSideReflection (T.vertex i) (T.vertex j) '' T.interiorSet) := by
  rw [Set.disjoint_left]
  rintro z hz ⟨w, hw, rfl⟩
  let B := T.affineBasis
  have hpos (v : ℂ) (hv : v ∈ T.interiorSet) : 0 < B.coord k (idealDiskKlein v) := by
    have hh : idealDiskKlein v ∈ interior (convexHull ℝ (range B)) := hv.2
    rw [B.interior_convexHull] at hh
    exact hh k
  have hn := (klein_coord_reflection_sign B i j k hij hjk hki
    (T.norm_vertex i) (T.norm_vertex j) (T.norm_vertex k) hw.1).mp (hpos _ hz).le
  exact (not_le_of_gt (hpos w hw)) hn

/-- The union of two reflected triangle interiors and their common complete open side is open in the disk plane. -/
theorem MarkedIdealDiskTriangle.isOpen_side_pair
    (T : MarkedIdealDiskTriangle) (hopen : IsOpen T.interiorSet)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    IsOpen (T.interiorSet ∪ T.openSide i j ∪
      idealDiskSideReflection (T.vertex i) (T.vertex j) '' T.interiorSet) := by
  let r := idealDiskSideReflectionPartial (T.vertex i) (T.vertex j)
    (T.norm_vertex i) (T.norm_vertex j) (T.distinct.ne hij)
  have hint : T.interiorSet ⊆ r.source := fun _ hz ↦ hz.1
  have himg : IsOpen (r '' T.interiorSet) := r.isOpen_image_of_subset_source hopen hint
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  rcases hx with (hx | hx) | hx
  · exact Filter.mem_of_superset (hopen.mem_nhds hx) (fun _ hz ↦ Or.inl (Or.inl hz))
  · obtain ⟨e, hxe, hsD, _, _, _, hrs, _, hequiv, hpos, _⟩ :=
      T.exists_oriented_side_coordinate i j k hij hjk hki hx
    apply Filter.mem_of_superset (e.open_source.mem_nhds hxe)
    intro z hz
    rcases lt_trichotomy 0 (e z).im with hp | he | hn
    · exact Or.inl (Or.inl ((hpos z hz).mpr hp))
    · have hfix : r z = z := e.injOn (hrs z hz) hz (by
        rw [hequiv z hz]
        exact Complex.conj_eq_iff_im.mpr he.symm)
      have heq := (idealDiskSideReflection_fixed_iff_sideEquation
        (T.norm_vertex i) (T.norm_vertex j) (T.distinct.ne hij) (hsD hz)).mp hfix
      apply Or.inl ∘ Or.inr
      rw [T.openSide_eq_native i j hij]
      exact ⟨hsD hz, heq⟩
    · have hrint : r z ∈ T.interiorSet := by
        apply (hpos _ (hrs z hz)).mpr
        rw [hequiv z hz, Complex.conj_im]
        exact neg_pos.mpr hn
      exact Or.inr ⟨r z, hrint, r.left_inv (hsD hz)⟩
  · exact Filter.mem_of_superset (himg.mem_nhds hx) (fun _ hz ↦ Or.inr hz)

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set Filter
open scoped ComplexConjugate _root_.Topology

/-- Doubling an upper-half-plane chart along an injectively parametrized real seam gives one biholomorphic chart on the whole open pair. -/
theorem exists_reflection_double_chart
    (F R : OpenPartialHomeomorph ℂ ℂ) (S : Set ℂ) (b : ℂ → ℂ)
    (hFt : F.target = {w : ℂ | 0 < w.im})
    (hRt : R.target = {w : ℂ | w.im < 0})
    (hFhol : DifferentiableOn ℂ F F.source)
    (hRhol : DifferentiableOn ℂ R R.source)
    (hdisj : Disjoint F.source R.source)
    (hsF : Disjoint S F.source) (hsR : Disjoint S R.source)
    (hb : ∀ z ∈ S, (b z).im = 0) (hbinj : InjOn b S)
    (hopen : IsOpen (F.source ∪ S ∪ R.source))
    (hseam : ∀ x ∈ S, ∃ H : OpenPartialHomeomorph ℂ ℂ,
      x ∈ H.source ∧ H.source ⊆ F.source ∪ S ∪ R.source ∧
      DifferentiableOn ℂ H H.source ∧
      EqOn H F (H.source ∩ F.source) ∧
      EqOn H R (H.source ∩ R.source) ∧ EqOn H b (H.source ∩ S)) :
    ∃ E : OpenPartialHomeomorph ℂ ℂ,
      E.source = F.source ∪ S ∪ R.source ∧
      DifferentiableOn ℂ E E.source ∧ DifferentiableOn ℂ E.symm E.target ∧
      EqOn E F F.source ∧ EqOn E R R.source ∧ EqOn E b S ∧
      E.target = F.target ∪ b '' S ∪ R.target := by
  classical
  let P := F.source ∪ S ∪ R.source
  let f : ℂ → ℂ := fun z ↦ if z ∈ F.source then F z else if z ∈ R.source then R z else b z
  have hfF : EqOn f F F.source := by
    intro z hz
    simp only [f, ite_eq_left hz]
  have hfR : EqOn f R R.source := by
    intro z hz
    have hn : z ∉ F.source := fun hh ↦ Set.disjoint_left.mp hdisj hh hz
    simp only [f, ite_eq_right hn, ite_eq_left hz]
  have hfb : EqOn f b S := by
    intro z hz
    have hnF : z ∉ F.source := fun hh ↦ Set.disjoint_left.mp hsF hz hh
    have hnR : z ∉ R.source := fun hh ↦ Set.disjoint_left.mp hsR hz hh
    simp only [f, ite_eq_right hnF, ite_eq_right hnR]
  have hfpos (z : ℂ) (hz : z ∈ F.source) : 0 < (f z).im := by
    rw [hfF hz]
    have hh := F.map_source hz
    rwa [hFt] at hh
  have hfneg (z : ℂ) (hz : z ∈ R.source) : (f z).im < 0 := by
    rw [hfR hz]
    have hh := R.map_source hz
    rwa [hRt] at hh
  have hfzero (z : ℂ) (hz : z ∈ S) : (f z).im = 0 := by rw [hfb hz]; exact hb z hz
  have hfhol : DifferentiableOn ℂ f P := by
    intro x hx
    rcases hx with (hx | hx) | hx
    · apply ((hFhol.differentiableAt (F.open_source.mem_nhds hx)).congr_of_eventuallyEq
        ?_).differentiableWithinAt
      filter_upwards [F.open_source.mem_nhds hx] with z hz
      exact hfF hz
    · obtain ⟨H, hxH, hHP, hHhol, hHF, hHR, hHb⟩ := hseam x hx
      apply ((hHhol.differentiableAt (H.open_source.mem_nhds hxH)).congr_of_eventuallyEq
        ?_).differentiableWithinAt
      filter_upwards [H.open_source.mem_nhds hxH] with z hz
      rcases hHP hz with (hzF | hzS) | hzR
      · exact (hfF hzF).trans (hHF ⟨hz, hzF⟩).symm
      · exact (hfb hzS).trans (hHb ⟨hz, hzS⟩).symm
      · exact (hfR hzR).trans (hHR ⟨hz, hzR⟩).symm
    · apply ((hRhol.differentiableAt (R.open_source.mem_nhds hx)).congr_of_eventuallyEq
        ?_).differentiableWithinAt
      filter_upwards [R.open_source.mem_nhds hx] with z hz
      exact hfR hz
  have hfinj : InjOn f P := by
    intro x hx y hy hxy
    have him := congrArg Complex.im hxy
    rcases hx with (hx | hx) | hx <;> rcases hy with (hy | hy) | hy
    · exact F.injOn hx hy ((hfF hx).symm.trans (hxy.trans (hfF hy)))
    · have hp := hfpos x hx
      have hz := hfzero y hy
      linarith
    · have hp := hfpos x hx
      have hn := hfneg y hy
      linarith
    · have hz := hfzero x hx
      have hp := hfpos y hy
      linarith
    · exact hbinj hx hy ((hfb hx).symm.trans (hxy.trans (hfb hy)))
    · have hz := hfzero x hx
      have hn := hfneg y hy
      linarith
    · have hn := hfneg x hx
      have hp := hfpos y hy
      linarith
    · have hn := hfneg x hx
      have hz := hfzero y hy
      linarith
    · exact R.injOn hx hy ((hfR hx).symm.trans (hxy.trans (hfR hy)))
  let E := holomorphicInjectivePartial f P hopen hfhol hfinj
  refine ⟨E, rfl, hfhol, holomorphicInjectivePartial_symm f P hopen hfhol hfinj,
    hfF, hfR, hfb, ?_⟩
  change f '' P = F.target ∪ b '' S ∪ R.target
  ext w
  constructor
  · rintro ⟨z, (hzF | hzS) | hzR, rfl⟩
    · rw [hfF hzF]
      exact Or.inl (Or.inl (F.map_source hzF))
    · exact Or.inl (Or.inr ⟨z, hzS, (hfb hzS).symm⟩)
    · rw [hfR hzR]
      exact Or.inr (R.map_source hzR)
  · rintro ((hwF | hwS) | hwR)
    · refine ⟨F.symm w, Or.inl (Or.inl (F.map_target hwF)), ?_⟩
      rw [hfF (F.map_target hwF), F.right_inv hwF]
    · obtain ⟨z, hz, rfl⟩ := hwS
      exact ⟨z, Or.inl (Or.inr hz), hfb hz⟩
    · refine ⟨R.symm w, Or.inr (R.map_target hwR), ?_⟩
      rw [hfR (R.map_target hwR), R.right_inv hwR]

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set
open scoped ComplexConjugate _root_.Topology

/-- The initial triangle and its neighbor across any chosen side form one biholomorphic sheet over the two half-planes joined through that side's real value interval. (Lyubich, §2.4.13) -/
theorem MarkedIdealDiskTriangle.exists_side_pair_chart
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hFs : F.source = T.interiorSet) (hFt : F.target = {w : ℂ | 0 < w.im})
    (hFhol : DifferentiableOn ℂ F F.source)
    (hclosure : closure T.interiorSet = T.closedSet)
    (b : ℂ → OnePoint ℂ) (hbcont : ContinuousOn b T.closedSet)
    (hbinj : InjOn b T.closedSet)
    (hbeq : EqOn b (fun z ↦ (F z : OnePoint ℂ)) T.interiorSet)
    (hb0 : b (T.vertex 0) = ((0 : ℂ) : OnePoint ℂ))
    (hb1 : b (T.vertex 1) = ((1 : ℂ) : OnePoint ℂ))
    (hb2 : b (T.vertex 2) = OnePoint.infty)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    ∃ E : OpenPartialHomeomorph ℂ ℂ,
      E.source = T.interiorSet ∪ T.openSide i j ∪
        idealDiskSideReflection (T.vertex i) (T.vertex j) '' T.interiorSet ∧
      DifferentiableOn ℂ E E.source ∧ DifferentiableOn ℂ E.symm E.target ∧
      EqOn E F T.interiorSet ∧
      EqOn E (fun z ↦ conj (F (idealDiskSideReflection (T.vertex i) (T.vertex j) z)))
        (idealDiskSideReflection (T.vertex i) (T.vertex j) '' T.interiorSet) ∧
      EqOn E (sphereFiniteValue b) (T.openSide i j) ∧
      E.target = {w : ℂ | 0 < w.im} ∪ sphereFiniteValue b '' T.openSide i j ∪
        {w : ℂ | w.im < 0} := by
  let r := idealDiskSideReflection (T.vertex i) (T.vertex j)
  let R := idealDiskReflectedChart (T.vertex i) (T.vertex j)
    (T.norm_vertex i) (T.norm_vertex j) (T.distinct.ne hij) F
  have hFD : F.source ⊆ {z : ℂ | ‖z‖ < 1} := fun z hz ↦ (hFs ▸ hz).1
  have hRs : R.source = r '' T.interiorSet := by
    rw [idealDiskReflectedChart_source _ _ _ _ _ F hFD, hFs]
  have hRt : R.target = {w : ℂ | w.im < 0} := by
    rw [idealDiskReflectedChart_target _ _ _ _ _ F hFD, hFt]
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      change -(v.im) < 0
      exact neg_neg_of_pos (show 0 < v.im from hv)
    · intro hw
      refine ⟨conj w, ?_, Complex.conj_conj w⟩
      change 0 < -w.im
      exact neg_pos.mpr hw
  have hRhol : DifferentiableOn ℂ R R.source :=
    idealDiskReflectedChart_differentiableOn _ _ _ _ _ F hFhol
  have hfix (z : ℂ) (hz : z ∈ T.openSide i j) : r z = z :=
    IdealDiskTriangle.idealDiskSideReflection_fixed_openSide
      (T.norm_vertex i) (T.norm_vertex j) (T.distinct.ne hij)
      ((T.openSide_eq_native i j hij) ▸ hz)
  have hdisj : Disjoint F.source R.source := by
    rw [hFs, hRs]
    exact T.reflection_interior_disjoint i j k hij hjk hki
  have hsF : Disjoint (T.openSide i j) F.source := by
    rw [hFs, Set.disjoint_left]
    exact fun z hz ↦ T.openSide_not_mem_interiorSet i j hz
  have hsR : Disjoint (T.openSide i j) R.source := by
    rw [Set.disjoint_left]
    intro z hz hzR
    have hrz : r z ∈ F.source := hzR.2
    rw [hfix z hz] at hrz
    exact Set.disjoint_left.mp hsF hz hrz
  have hfinite (z : ℂ) (hz : z ∈ T.openSide i j) : b z ≠ OnePoint.infty := by
    obtain ⟨w, hw, _, _⟩ := T.sphere_extension_disk_value b hbinj hb0 hb1 hb2
      (T.openSide_subset_closedSet i j hz) hz.1
    rw [hw]
    exact OnePoint.coe_ne_infty w
  have hbreal (z : ℂ) (hz : z ∈ T.openSide i j) : (sphereFiniteValue b z).im = 0 := by
    apply chart_sphere_extension_frontier_real F hFt b
      (by simpa only [hFs, hclosure] using hbcont)
      (by simpa only [hFs] using hbeq)
    · rw [hFs]
      exact T.openSide_subset_frontier hclosure (hFs ▸ F.open_source) i j hz
    · exact (sphereFiniteValue_coe b (hfinite z hz)).symm
  have hBinj : InjOn (sphereFiniteValue b) (T.openSide i j) :=
    sphereFiniteValue_injOn b (hbinj.mono (T.openSide_subset_closedSet i j)) hfinite
  have hopen : IsOpen (F.source ∪ T.openSide i j ∪ R.source) := by
    rw [hFs, hRs]
    exact T.isOpen_side_pair (hFs ▸ F.open_source) i j k hij hjk hki
  have hseam (x : ℂ) (hx : x ∈ T.openSide i j) :
      ∃ H : OpenPartialHomeomorph ℂ ℂ, x ∈ H.source ∧
        H.source ⊆ F.source ∪ T.openSide i j ∪ R.source ∧
        DifferentiableOn ℂ H H.source ∧ EqOn H F (H.source ∩ F.source) ∧
        EqOn H R (H.source ∩ R.source) ∧ EqOn H (sphereFiniteValue b) (H.source ∩ T.openSide i j) := by
    obtain ⟨H, hxH, _, hHP, hHhol, _, hHF, hHb, hrs, hconj⟩ :=
      T.exists_side_extension F hFs hFt hFhol hclosure b hbcont hbinj hbeq hb0 hb1 hb2
        i j k hij hjk hki hx
    refine ⟨H, hxH, by simpa only [hFs, hRs] using hHP, hHhol,
      by simpa only [hFs] using hHF, ?_, ?_⟩
    · intro z hz
      have hrz : r z ∈ T.interiorSet := hFs ▸ hz.2.2
      have hh := hHF ⟨hrs z hz.1, hrz⟩
      change H z = conj (F (r z))
      rw [← hh, hconj z hz.1, Complex.conj_conj]
    · intro z hz
      exact OnePoint.coe_injective ((hHb z ⟨hz.1, T.openSide_subset_closedSet i j hz.2⟩).trans
        (sphereFiniteValue_coe b (hfinite z hz.2)).symm)
  obtain ⟨E, hEs, hEhol, hEinv, hEF, hER, hEb, hEt⟩ :=
    exists_reflection_double_chart F R (T.openSide i j) (sphereFiniteValue b) hFt hRt hFhol
      hRhol hdisj hsF hsR hbreal hBinj hopen hseam
  refine ⟨E, by simpa only [hFs, hRs] using hEs, hEhol, hEinv,
    by simpa only [hFs] using hEF, ?_, hEb, ?_⟩
  · intro z hz
    have hh := hER (hRs.symm ▸ hz)
    change E z = conj (F (r z)) at hh
    exact hh
  · simpa only [hFt, hRt] using hEt

end HolomorphicAnosov

namespace HolomorphicAnosov
open scoped ComplexConjugate

/-- Immediate backtracks in the reflection word give the same analytic chart. -/
theorem MarkedIdealDiskTriangle.itineraryChart_eqOn_cancel_backtrack
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hF : F.source ⊆ {z : ℂ | ‖z‖ < 1})
    (u v : List (Fin 3)) (i : Fin 3) :
    (T.itineraryChart F (u ++ i :: i :: v)).source =
        (T.itineraryChart F (u ++ v)).source ∧
      Set.EqOn (T.itineraryChart F (u ++ i :: i :: v))
        (T.itineraryChart F (u ++ v))
        (T.itineraryChart F (u ++ i :: i :: v)).source := by
  apply T.itineraryChart_eqOn_of_transport_eq F hF
  · intro z hz
    exact T.itineraryMap_cancel_backtrack u v i (hF hz)
  · funext z
    simp only [List.length_append, List.length_cons, Function.iterate_add_apply,
      Function.iterate_one]
    simp only [Complex.conj_conj]

/-- Evaluation on a cancelled reflected word agrees at every point of the original chart source. -/
theorem MarkedIdealDiskTriangle.itineraryChart_apply_cancel_backtrack
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hF : F.source ⊆ {z : ℂ | ‖z‖ < 1})
    (u v : List (Fin 3)) (i : Fin 3) {z : ℂ} (hz : z ∈ F.source) :
    T.itineraryChart F (u ++ i :: i :: v) (T.itineraryMap (u ++ v) z) =
      T.itineraryChart F (u ++ v) (T.itineraryMap (u ++ v) z) := by
  obtain ⟨hs, heq⟩ := T.itineraryChart_eqOn_cancel_backtrack F hF u v i
  apply heq
  rw [hs, T.itineraryChart_source F hF (u ++ v)]
  exact Set.mem_image_of_mem _ hz

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set
open scoped ComplexConjugate

/-- Two charts that agree on a common source subset continue to agree on its image under any reflection word. -/
theorem MarkedIdealDiskTriangle.itineraryChart_eqOn_transport
    (T : MarkedIdealDiskTriangle) (E F : OpenPartialHomeomorph ℂ ℂ)
    (hED : E.source ⊆ {z : ℂ | ‖z‖ < 1})
    (hFD : F.source ⊆ {z : ℂ | ‖z‖ < 1})
    (S : Set ℂ) (hSE : S ⊆ E.source) (hSF : S ⊆ F.source)
    (hEF : EqOn E F S) (w : List (Fin 3)) :
    EqOn (T.itineraryChart E w) (T.itineraryChart F w) (T.itineraryMap w '' S) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [T.itineraryChart_apply E hED w (hSE hx),
    T.itineraryChart_apply F hFD w (hSF hx), hEF hx]

/-- The full adjacent-pair chart transports through any reflection word. -/
theorem MarkedIdealDiskTriangle.transported_side_pair_chart
    (T : MarkedIdealDiskTriangle) (F E : OpenPartialHomeomorph ℂ ℂ)
    (hFs : F.source = T.interiorSet)
    (hEhol : DifferentiableOn ℂ E E.source)
    (hEinv : DifferentiableOn ℂ E.symm E.target)
    (b : ℂ → ℂ) (i : Fin 3)
    (hEs : E.source = T.interiorSet ∪ T.openSide i (i + 1) ∪
      idealDiskSideReflection (T.vertex i) (T.vertex (i + 1)) '' T.interiorSet)
    (hEF : EqOn E F T.interiorSet)
    (hER : EqOn E (fun z ↦ conj (F (idealDiskSideReflection
        (T.vertex i) (T.vertex (i + 1)) z)))
      (idealDiskSideReflection (T.vertex i) (T.vertex (i + 1)) '' T.interiorSet))
    (hEb : EqOn E b (T.openSide i (i + 1))) (w : List (Fin 3)) :
    let D := T.itineraryChart E w
    D.source = T.itineraryMap w '' E.source ∧
      D.source ⊆ {z : ℂ | ‖z‖ < 1} ∧
      D.target = (conj^[w.length]) '' E.target ∧
      DifferentiableOn ℂ D D.source ∧ DifferentiableOn ℂ D.symm D.target ∧
      EqOn D (T.itineraryChart F w) (T.itineraryMap w '' T.interiorSet) ∧
      EqOn D (T.itineraryChart F (w ++ [i]))
        (T.itineraryMap w '' (idealDiskSideReflection
          (T.vertex i) (T.vertex (i + 1)) '' T.interiorSet)) ∧
      ∀ z ∈ T.openSide i (i + 1),
        D (T.itineraryMap w z) = (conj^[w.length]) (b z) := by
  have hFD : F.source ⊆ {z : ℂ | ‖z‖ < 1} := fun z hz ↦ (hFs ▸ hz).1
  have hED : E.source ⊆ {z : ℂ | ‖z‖ < 1} := by
    rw [hEs]
    rintro z ((hz | hz) | ⟨x, hx, rfl⟩)
    · exact hz.1
    · exact hz.1
    · exact IdealDiskTriangle.idealDiskSideReflection_mem_disk_g6
        (T.norm_vertex i) (T.norm_vertex (i + 1)) (T.vertex_ne_next i) hx.1
  have hIE : T.interiorSet ⊆ E.source := by
    intro z hz
    rw [hEs]
    exact Or.inl (Or.inl hz)
  have hRE : idealDiskSideReflection (T.vertex i) (T.vertex (i + 1)) ''
      T.interiorSet ⊆ E.source := by
    intro z hz
    rw [hEs]
    exact Or.inr hz
  have hSE : T.openSide i (i + 1) ⊆ E.source := by
    intro z hz
    rw [hEs]
    exact Or.inl (Or.inr hz)
  dsimp only
  refine ⟨T.itineraryChart_source E hED w,
    T.itineraryChart_source_subset E hED w,
    T.itineraryChart_target E hED w,
    (T.itineraryChart_biholomorphic E hED hEhol hEinv w).1,
    (T.itineraryChart_biholomorphic E hED hEhol hEinv w).2,
    T.itineraryChart_eqOn_transport E F hED hFD T.interiorSet hIE
      (by rw [hFs]) hEF w, ?_, ?_⟩
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hrx : idealDiskSideReflection (T.vertex i) (T.vertex (i + 1)) x ∈ E.source :=
      hRE ⟨x, hx, rfl⟩
    rw [T.itineraryChart_apply E hED w hrx, hER ⟨x, hx, rfl⟩]
    dsimp only
    rw [IdealDiskTriangle.idealDiskSideReflection_involutive_disk_g6
        (T.norm_vertex i) (T.norm_vertex (i + 1)) (T.vertex_ne_next i) x hx.1]
    have hm : T.itineraryMap w (idealDiskSideReflection
        (T.vertex i) (T.vertex (i + 1)) x) = T.itineraryMap (w ++ [i]) x := by
      rw [T.itineraryMap_append, T.itineraryMap_cons]
      rfl
    rw [hm, T.itineraryChart_apply F hFD (w ++ [i]) (hFs.symm ▸ hx)]
    simp only [List.length_append, List.length_singleton, Function.iterate_add_apply,
      Function.iterate_one]
  · intro z hz
    rw [T.itineraryChart_apply E hED w (hSE hz), hEb hz]

end HolomorphicAnosov
