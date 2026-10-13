import HolomorphicAnosov.Topology.TriangleInteriorCoordinatesG2

open Set
namespace HolomorphicAnosov

/-- Reflection of the first coordinate, used for the two halves of a triangle. -/
def horizontalReflectG2 : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearEquiv.neg ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

lemma negative_standard_triangle_hull_g2 :
    convexHull ℝ ({(0,0),(0,1),(-1,0)} : Set (ℝ × ℝ)) =
      {p | p.1 ≤ 0 ∧ 0 ≤ p.2 ∧ -p.1+p.2 ≤ 1} := by
  have he : horizontalReflectG2 '' convexHull ℝ ({(0,0),(0,1),(1,0)} : Set (ℝ × ℝ)) =
      convexHull ℝ ({(0,0),(0,1),(-1,0)} : Set (ℝ × ℝ)) := by
    change horizontalReflectG2.toLinearMap '' convexHull ℝ _ = _
    rw [LinearMap.image_convexHull]
    congr 1
    simp [horizontalReflectG2]
  rw [← he,standard_triangle_hull_g2]
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    change -q.1 ≤ 0 ∧ 0 ≤ q.2 ∧ -(-q.1)+q.2 ≤ 1
    simpa using hq
  · intro hp
    exact ⟨(-p.1,p.2),⟨by linarith [hp.1],hp.2⟩,by simp [horizontalReflectG2]⟩

lemma negative_standard_triangle_interior_g2 :
    interior (convexHull ℝ ({(0,0),(0,1),(-1,0)} : Set (ℝ × ℝ))) =
      {p | p.1 < 0 ∧ 0 < p.2 ∧ -p.1+p.2 < 1} := by
  have he : horizontalReflectG2 '' convexHull ℝ ({(0,0),(0,1),(1,0)} : Set (ℝ × ℝ)) =
      convexHull ℝ ({(0,0),(0,1),(-1,0)} : Set (ℝ × ℝ)) := by
    change horizontalReflectG2.toLinearMap '' convexHull ℝ _ = _
    rw [LinearMap.image_convexHull]
    congr 1
    simp [horizontalReflectG2]
  rw [← he]
  change interior (horizontalReflectG2.toHomeomorph '' _) = _
  rw [← horizontalReflectG2.toHomeomorph.image_interior,standard_triangle_interior_g2]
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    change -q.1 < 0 ∧ 0 < q.2 ∧ -(-q.1)+q.2 < 1
    simpa using hq
  · intro hp
    exact ⟨(-p.1,p.2),⟨by linarith [hp.1],hp.2⟩,by simp [horizontalReflectG2]⟩

/-- The interiors of two right triangles with opposite equal horizontal legs,
together with their common open vertical edge, form an open planar region.
Their closed intersection is precisely the common edge, and each interior
avoids the other closed triangle.

Source: Cairns (1951), §4(B), p.864. Perpendicular coordinates identify the two
closed triangles with 0≤v, 0≤±u, ±u+v≤1. Their interiors use strict inequalities.
The joined open region is v>0, u+v<1, -u+v<1, an intersection of three open
halfplanes. The common closed locus has u=0 and 0≤v≤1. -/
theorem two_triangle_seam_geometry_g2
    (M D1 D2 P : ℂ) (hD : D2 ≠ M) (hP : P ≠ M)
    (hmid : D1-M=-(D2-M))
    (hperp : (D2-M).re*(P-M).re+(D2-M).im*(P-M).im=0) :
    let T1 := convexHull ℝ {M,P,D1}
    let T2 := convexHull ℝ {M,P,D2}
    IsOpen (interior T1 ∪ interior T2 ∪ openSegment ℝ M P) ∧
      T1 ∩ T2 = segment ℝ M P ∧
      Disjoint (interior T1) T2 ∧ Disjoint T1 (interior T2) := by
  intro T1 T2
  obtain ⟨F,hF⟩ := perpendicular_triangle_coordinates_g2 M (D2-M) (P-M)
    (sub_ne_zero.mpr hD) (sub_ne_zero.mpr hP) hperp
  have hF0 : F (0,0)=M := by simp [hF]
  have hFp : F (0,1)=P := by simp [hF]
  have hF2 : F (1,0)=D2 := by simp [hF]
  have hF1 : F (-1,0)=D1 := by
    rw [hF]
    simp only [neg_one_smul,zero_smul,add_zero]
    rw [← hmid]
    abel
  have hT1 : F '' convexHull ℝ ({(0,0),(0,1),(-1,0)} : Set (ℝ × ℝ)) = T1 := by
    change F.toAffineEquiv.toAffineMap '' convexHull ℝ _ = _
    rw [F.toAffineEquiv.toAffineMap.image_convexHull]
    congr 1
    change F '' _ = _
    simp only [image_insert_eq,image_singleton,hF0,hFp,hF1]
  have hT2 : F '' convexHull ℝ ({(0,0),(0,1),(1,0)} : Set (ℝ × ℝ)) = T2 := by
    change F.toAffineEquiv.toAffineMap '' convexHull ℝ _ = _
    rw [F.toAffineEquiv.toAffineMap.image_convexHull]
    congr 1
    change F '' _ = _
    simp only [image_insert_eq,image_singleton,hF0,hFp,hF2]
  have hmem1 (q : ℝ × ℝ) : F q ∈ T1 ↔ q.1 ≤ 0 ∧ 0 ≤ q.2 ∧ -q.1+q.2 ≤ 1 := by
    rw [← hT1,F.injective.mem_set_image,negative_standard_triangle_hull_g2]
    rfl
  have hmem2 (q : ℝ × ℝ) : F q ∈ T2 ↔ 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1+q.2 ≤ 1 := by
    rw [← hT2,F.injective.mem_set_image,standard_triangle_hull_g2]
    rfl
  have hint1 (q : ℝ × ℝ) : F q ∈ interior T1 ↔ q.1 < 0 ∧ 0 < q.2 ∧ -q.1+q.2 < 1 := by
    rw [← hT1]
    change F.toHomeomorph q ∈ interior (F.toHomeomorph '' _) ↔ _
    rw [← F.toHomeomorph.image_interior,F.toHomeomorph.injective.mem_set_image,negative_standard_triangle_interior_g2]
    rfl
  have hint2 (q : ℝ × ℝ) : F q ∈ interior T2 ↔ 0 < q.1 ∧ 0 < q.2 ∧ q.1+q.2 < 1 := by
    rw [← hT2]
    change F.toHomeomorph q ∈ interior (F.toHomeomorph '' _) ↔ _
    rw [← F.toHomeomorph.image_interior,F.toHomeomorph.injective.mem_set_image,standard_triangle_interior_g2]
    rfl
  have hseg (q : ℝ × ℝ) : F q ∈ segment ℝ M P ↔ q.1=0 ∧ q.2 ∈ Icc (0:ℝ) 1 := by
    constructor
    · rintro ⟨a,b,ha,hb,hab,he⟩
      have hFq : F (0,b)=F q := by
        rw [hF]
        simp only [zero_smul,add_zero]
        rw [← he]
        calc
          M+b • (P-M)=a • M+b • P+(1-a-b) • M := by module
          _ = a • M+b • P := by rw [show 1-a-b=0 by linarith]; simp
      have heq := F.injective hFq
      rw [← heq]
      exact ⟨rfl,⟨hb,by linarith⟩⟩
    · rintro ⟨h0,hy⟩
      refine ⟨1-q.2,q.2,by linarith [hy.2],hy.1,by ring,?_⟩
      rw [hF,h0]
      simp only [zero_smul,add_zero]
      module
  have hopenSeg (q : ℝ × ℝ) : F q ∈ openSegment ℝ M P ↔ q.1=0 ∧ q.2 ∈ Ioo (0:ℝ) 1 := by
    constructor
    · intro hq
      have hc := (hseg q).mp (openSegment_subset_segment ℝ _ _ hq)
      refine ⟨hc.1,?_,?_⟩
      · apply lt_of_le_of_ne hc.2.1
        intro he
        have hqm : F q=M := by rw [hF,hc.1,← he]; simp
        exact hP.symm (left_mem_openSegment_iff.mp (hqm ▸ hq))
      · apply lt_of_le_of_ne hc.2.2
        intro he
        have hqp : F q=P := by rw [hF,hc.1,he]; simp
        exact hP.symm (right_mem_openSegment_iff.mp (hqp ▸ hq))
    · rintro ⟨h0,hy⟩
      refine ⟨1-q.2,q.2,by linarith [hy.2],hy.1,by ring,?_⟩
      rw [hF,h0]
      simp only [zero_smul,add_zero]
      module
  have hjoin : interior T1 ∪ interior T2 ∪ openSegment ℝ M P =
      F '' {q : ℝ × ℝ | 0 < q.2 ∧ q.1+q.2<1 ∧ -q.1+q.2<1} := by
    ext z
    obtain ⟨q,rfl⟩ := F.surjective z
    rw [F.injective.mem_set_image]
    simp only [mem_union,hint1,hint2,hopenSeg,mem_Ioo,mem_ofPred_eq]
    constructor
    · rintro ((h | h) | h) <;> exact ⟨h.2.1,by linarith [h.1,h.2.2],by linarith [h.1,h.2.2]⟩
    · intro h
      rcases lt_trichotomy q.1 0 with hneg | hzero | hpos
      · exact Or.inl (Or.inl ⟨hneg,h.1,h.2.2⟩)
      · exact Or.inr ⟨hzero,h.1,by linarith [h.2.1]⟩
      · exact Or.inl (Or.inr ⟨hpos,h.1,h.2.1⟩)
  refine ⟨?_,?_,?_,?_⟩
  · rw [hjoin]
    apply F.toHomeomorph.isOpenMap
    exact (isOpen_lt continuous_const continuous_snd).inter
      ((isOpen_lt (continuous_fst.add continuous_snd) continuous_const).inter
        (isOpen_lt (continuous_fst.neg.add continuous_snd) continuous_const))
  · ext z
    obtain ⟨q,rfl⟩ := F.surjective z
    rw [mem_inter_iff,hmem1,hmem2,hseg]
    constructor
    · rintro ⟨h1,h2⟩
      exact ⟨by linarith [h1.1,h2.1],h1.2.1,by linarith [h1.2.2,h2.2.2]⟩
    · rintro ⟨h0,hy⟩
      simp only [h0,neg_zero,zero_add]
      exact ⟨⟨le_rfl,hy⟩,⟨le_rfl,hy⟩⟩
  · apply disjoint_left.mpr
    intro z hz1 hz2
    obtain ⟨q,rfl⟩ := F.surjective z
    exact ((hint1 q).mp hz1).1.not_ge ((hmem2 q).mp hz2).1
  · apply disjoint_left.mpr
    intro z hz1 hz2
    obtain ⟨q,rfl⟩ := F.surjective z
    exact ((hint2 q).mp hz2).1.not_ge ((hmem1 q).mp hz1).1

end HolomorphicAnosov
