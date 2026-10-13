import HolomorphicAnosov.Topology.HalfSectorVisibleCompactG2
import Mathlib.Analysis.Normed.Operator.Banach

open Set
namespace HolomorphicAnosov

lemma standard_triangle_interior_g2 :
    interior (convexHull ℝ ({(0,0),(0,1),(1,0)} : Set (ℝ × ℝ))) =
      {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1+p.2 < 1} := by
  let sum : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ
  have hsum : IsOpenMap sum := sum.isOpenMap (fun x ↦ ⟨(x,0),by simp [sum]⟩)
  rw [standard_triangle_hull_g2]
  change interior ((Prod.fst ⁻¹' Ici (0:ℝ)) ∩
    ((Prod.snd ⁻¹' Ici (0:ℝ)) ∩ (sum ⁻¹' Iic (1:ℝ)))) = _
  rw [interior_inter,interior_inter,
    ← isOpenMap_fst.preimage_interior_eq_interior_preimage continuous_fst,
    ← isOpenMap_snd.preimage_interior_eq_interior_preimage continuous_snd,
    ← hsum.preimage_interior_eq_interior_preimage sum.continuous,
    interior_Ici,interior_Iic]
  ext p
  simp only [mem_inter_iff,mem_preimage,mem_Ioi,mem_Iio]
  change (0 < p.1 ∧ 0 < p.2 ∧ p.1+p.2 < 1) ↔ _
  rfl

/-- A nondegenerate perpendicular triangle has nonempty interior, its apex is
in the closure of that interior, and its two apex edges avoid the interior.

Source: Cairns (1951), §3, p.862, triangle setup. In perpendicular affine
coordinates the triangle is u,v≥0, u+v≤1 and its interior is given by all three
strict inequalities. The point (1/3,1/3) is interior. Convexity makes the closed
triangle the closure of its interior. The two apex edges have one coordinate
zero, so neither intersects the interior. -/
theorem perpendicular_triangle_interior_g2 (M D P : ℂ) (hD : D ≠ M) (hP : P ≠ M)
    (hperp : (D-M).re*(P-M).re+(D-M).im*(P-M).im=0) :
    (interior (convexHull ℝ {M,P,D})).Nonempty ∧
    M ∈ closure (interior (convexHull ℝ {M,P,D})) ∧
    Disjoint (interior (convexHull ℝ {M,P,D})) (segment ℝ M D ∪ segment ℝ M P) := by
  obtain ⟨F,hF⟩ := perpendicular_triangle_coordinates_g2 M (D-M) (P-M)
    (sub_ne_zero.mpr hD) (sub_ne_zero.mpr hP) hperp
  have hF0 : F (0,0) = M := by simp [hF]
  have hF1 : F (1,0) = D := by simp [hF]
  have hF2 : F (0,1) = P := by simp [hF]
  let T := convexHull ℝ ({(0,0),(0,1),(1,0)} : Set (ℝ × ℝ))
  have hFT : F '' T = convexHull ℝ {M,P,D} := by
    change F.toAffineEquiv.toAffineMap '' convexHull ℝ _ = _
    rw [F.toAffineEquiv.toAffineMap.image_convexHull]
    congr 1
    change F '' _ = _
    simp only [image_insert_eq,image_singleton,hF0,hF1,hF2]
  have hFi : F '' interior T = interior (convexHull ℝ {M,P,D}) := by
    change F.toHomeomorph '' interior T = _
    rw [F.toHomeomorph.image_interior]
    exact congrArg interior hFT
  have hne : (interior (convexHull ℝ {M,P,D})).Nonempty := by
    rw [← hFi]
    refine ⟨F (1/3,1/3),⟨(1/3,1/3),?_,rfl⟩⟩
    rw [show interior T = _ from standard_triangle_interior_g2]
    norm_num
  refine ⟨hne,?_,?_⟩
  · rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior hne]
    exact subset_closure (subset_convexHull ℝ _ (by simp))
  · apply disjoint_left.mpr
    intro q hqi hqe
    rw [← hFi] at hqi
    obtain ⟨p,hp,rfl⟩ := hqi
    have hp' : 0 < p.1 ∧ 0 < p.2 ∧ p.1+p.2 < 1 := by
      rwa [standard_triangle_interior_g2] at hp
    have hseg : ∀ v : ℝ × ℝ,
        segment ℝ M (F v) = F '' segment ℝ (0,0) v := by
      intro v
      have hs := (image_segment ℝ F.toAffineEquiv.toAffineMap (0,0) v).symm
      change segment ℝ (F (0,0)) (F v) = F '' segment ℝ (0,0) v at hs
      simpa only [hF0] using hs
    rcases hqe with hqe | hqe
    · rw [← hF1,hseg] at hqe
      obtain ⟨r,hr,hrp⟩ := hqe
      have hrp' := F.injective hrp
      subst r
      obtain ⟨a,b,ha,hb,hab,he⟩ := hr
      have he2 := congrArg Prod.snd he
      simp only [Prod.snd_add,Prod.smul_snd,smul_eq_mul,mul_zero,add_zero] at he2
      exact hp'.2.1.ne' he2.symm
    · rw [← hF2,hseg] at hqe
      obtain ⟨r,hr,hrp⟩ := hqe
      have hrp' := F.injective hrp
      subst r
      obtain ⟨a,b,ha,hb,hab,he⟩ := hr
      have he1 := congrArg Prod.fst he
      simp only [Prod.fst_add,Prod.smul_fst,smul_eq_mul,mul_zero,add_zero] at he1
      exact hp'.1.ne' he1.symm

/-- A strict radial segment to a triangle point off the two apex edges lies
in the triangle interior. Source: the same triangle-coordinate calculation as
`perpendicular_triangle_interior_g2`: positive coordinates stay positive, while
strict radial scaling makes their sum less than one. -/
lemma perpendicular_triangle_radial_interior_g2
    (M D P : ℂ) (hD : D ≠ M) (hP : P ≠ M)
    (hperp : (D-M).re*(P-M).re+(D-M).im*(P-M).im=0)
    {Q : ℂ} (hQ : Q ∈ convexHull ℝ {M,P,D})
    (hQaxes : Q ∉ segment ℝ M D ∪ segment ℝ M P) :
    openSegment ℝ M Q ⊆ interior (convexHull ℝ {M,P,D}) := by
  obtain ⟨F,hF⟩ := perpendicular_triangle_coordinates_g2 M (D-M) (P-M)
    (sub_ne_zero.mpr hD) (sub_ne_zero.mpr hP) hperp
  have hF0 : F (0,0) = M := by simp [hF]
  have hF1 : F (1,0) = D := by simp [hF]
  have hF2 : F (0,1) = P := by simp [hF]
  let T := convexHull ℝ ({(0,0),(0,1),(1,0)} : Set (ℝ × ℝ))
  have hFT : F '' T = convexHull ℝ {M,P,D} := by
    change F.toAffineEquiv.toAffineMap '' convexHull ℝ _ = _
    rw [F.toAffineEquiv.toAffineMap.image_convexHull]
    congr 1
    change F '' _ = _
    simp only [image_insert_eq,image_singleton,hF0,hF1,hF2]
  have hFi : F '' interior T = interior (convexHull ℝ {M,P,D}) := by
    change F.toHomeomorph '' interior T = _
    rw [F.toHomeomorph.image_interior]
    exact congrArg interior hFT
  rw [← hFT] at hQ
  obtain ⟨p,hp,rfl⟩ := hQ
  have hp' : 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1+p.2 ≤ 1 := by
    simpa only [T,standard_triangle_hull_g2,Set.mem_ofPred_eq] using hp
  have hp1 : 0 < p.1 := lt_of_le_of_ne hp'.1 (by
    intro hz
    apply hQaxes
    right
    refine ⟨1-p.2,p.2,by linarith [hp'.2.2],hp'.2.1,by ring,?_⟩
    rw [hF]
    simp only [← hz,zero_smul,add_zero]
    module)
  have hp2 : 0 < p.2 := lt_of_le_of_ne hp'.2.1 (by
    intro hz
    apply hQaxes
    left
    refine ⟨1-p.1,p.1,by linarith [hp'.2.2],hp'.1,by ring,?_⟩
    rw [hF]
    simp only [← hz,zero_smul,add_zero]
    module)
  intro x hx
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨t,ht,rfl⟩ := hx
  rw [← hFi]
  refine ⟨(t*p.1,t*p.2),?_,?_⟩
  · rw [show interior T = _ from standard_triangle_interior_g2]
    refine ⟨mul_pos ht.1 hp1,mul_pos ht.1 hp2,?_⟩
    change t*p.1+t*p.2<1
    nlinarith [ht.2,mul_nonneg ht.1.le (sub_nonneg.mpr hp'.2.2)]
  · rw [hF,hF,AffineMap.lineMap_apply_module]
    module

/-- The opposite base also avoids the triangle interior, since its coordinate
sum is one while interior points have coordinate sum strictly less than one. -/
lemma perpendicular_triangle_base_disjoint_interior_g2
    (M D P : ℂ) (hD : D ≠ M) (hP : P ≠ M)
    (hperp : (D-M).re*(P-M).re+(D-M).im*(P-M).im=0) :
    Disjoint (interior (convexHull ℝ {M,P,D})) (segment ℝ D P) := by
  obtain ⟨F,hF⟩ := perpendicular_triangle_coordinates_g2 M (D-M) (P-M)
    (sub_ne_zero.mpr hD) (sub_ne_zero.mpr hP) hperp
  have hF0 : F (0,0)=M := by simp [hF]
  have hF1 : F (1,0)=D := by simp [hF]
  have hF2 : F (0,1)=P := by simp [hF]
  let T := convexHull ℝ ({(0,0),(0,1),(1,0)} : Set (ℝ × ℝ))
  have hFT : F '' T = convexHull ℝ {M,P,D} := by
    change F.toAffineEquiv.toAffineMap '' convexHull ℝ _ = _
    rw [F.toAffineEquiv.toAffineMap.image_convexHull]
    congr 1
    change F '' _ = _
    simp only [image_insert_eq,image_singleton,hF0,hF1,hF2]
  have hFi : F '' interior T = interior (convexHull ℝ {M,P,D}) := by
    change F.toHomeomorph '' interior T = _
    rw [F.toHomeomorph.image_interior]
    exact congrArg interior hFT
  apply disjoint_left.mpr
  intro x hx hxb
  rw [← hFi] at hx
  obtain ⟨p,hp,rfl⟩ := hx
  have hp' : 0 < p.1 ∧ 0 < p.2 ∧ p.1+p.2<1 := by
    simpa only [T,standard_triangle_interior_g2,Set.mem_ofPred_eq] using hp
  obtain ⟨a,b,ha,hb,hab,he⟩ := hxb
  have hfp : F (a,b)=F p := by
    rw [hF]
    rw [← he]
    calc
      M+a • (D-M)+b • (P-M) = a • D+b • P+(1-a-b) • M := by module
      _ = a • D+b • P := by rw [show 1-a-b=0 by linarith]; simp
  have hpab : (a,b)=p := F.injective hfp
  have hpSum : p.1+p.2=1 := by rw [← hpab]; exact hab
  exact hp'.2.2.ne hpSum

/-- The two incident edges of a nondegenerate perpendicular triangle meet
only at the apex. Their inverse affine coordinates lie on distinct axes. -/
lemma perpendicular_triangle_axes_intersection_g2
    (M D P : ℂ) (hD : D ≠ M) (hP : P ≠ M)
    (hperp : (D-M).re*(P-M).re+(D-M).im*(P-M).im=0) :
    segment ℝ M D ∩ segment ℝ M P = {M} := by
  obtain ⟨F,hF⟩ := perpendicular_triangle_coordinates_g2 M (D-M) (P-M)
    (sub_ne_zero.mpr hD) (sub_ne_zero.mpr hP) hperp
  apply Subset.antisymm
  · rintro x ⟨⟨a,b,ha,hb,hab,he⟩,⟨c,d,hc,hd,hcd,hf⟩⟩
    have hFb : F (b,0)=x := by
      rw [hF]
      simp only [zero_smul,add_zero]
      rw [← he]
      calc
        M+b • (D-M)=a • M+b • D+(1-a-b) • M := by module
        _ = a • M+b • D := by rw [show 1-a-b=0 by linarith]; simp
    have hFd : F (0,d)=x := by
      rw [hF]
      simp only [zero_smul,add_zero]
      rw [← hf]
      calc
        M+d • (P-M)=c • M+d • P+(1-c-d) • M := by module
        _ = c • M+d • P := by rw [show 1-c-d=0 by linarith]; simp
    have hb0 : b=0 := congrArg Prod.fst (F.injective (hFb.trans hFd.symm))
    have ha1 : a=1 := by linarith
    simpa [hb0,ha1] using he.symm
  · rintro x rfl
    exact ⟨left_mem_segment ℝ _ _,left_mem_segment ℝ _ _⟩

end HolomorphicAnosov
