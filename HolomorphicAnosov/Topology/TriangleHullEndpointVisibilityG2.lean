import HolomorphicAnosov.Topology.HalfSectorVisibleCompactG2

open Set
namespace HolomorphicAnosov

lemma convex_affine_nonneg_singleton_fiber_g2
    {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E →ᵃ[ℝ] ℝ) (q : E) :
    Convex ℝ {x | 0 ≤ f x ∧ (f x=0 → x=q)} := by
  intro x hx y hy a b ha hb hab
  have hf : f (a • x+b • y)=a*f x+b*f y := by
    simpa only [smul_eq_mul] using (Convex.combo_affine_apply (f := f) (x := x) (y := y) hab)
  refine ⟨by rw [hf]; exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),?_⟩
  intro hz
  rw [hf] at hz
  by_cases ha0 : a=0
  · have hb1 : b=1 := by linarith
    have hy0 : f y=0 := by simpa [ha0,hb1] using hz
    simp [ha0,hb1,hy.2 hy0]
  by_cases hb0 : b=0
  · have ha1 : a=1 := by linarith
    have hx0 : f x=0 := by simpa [hb0,ha1] using hz
    simp [hb0,ha1,hx.2 hx0]
  have hax : a*f x=0 := le_antisymm (by nlinarith [mul_nonneg hb hy.1]) (mul_nonneg ha hx.1)
  have hby : b*f y=0 := le_antisymm (by nlinarith [mul_nonneg ha hx.1]) (mul_nonneg hb hy.1)
  rw [hx.2 ((mul_eq_zero.mp hax).resolve_left ha0),hy.2 ((mul_eq_zero.mp hby).resolve_left hb0),← add_smul,hab,one_smul]

/-- In the Cairns triangle hull, the two base vertices are visible from the
apex if its two incident edges have no generator contacts except those vertices.

Source: Cairns (1951), §3 Case II, p.863. Use perpendicular affine coordinates.
Each coordinate is nonnegative on the generator. Its zero fiber contains only
the opposite axis vertex, and the convex set consisting of the positive
halfspace plus that one vertex contains the entire hull. Thus the hull meets
either apex edge before its far endpoint, which is precisely endpoint visibility. -/
theorem triangle_hull_endpoints_visible_g2
    (M D P : ℂ) (hD : D ≠ M) (hP : P ≠ M)
    (hperp : (D-M).re*(P-M).re+(D-M).im*(P-M).im=0)
    (C : Set ℂ)
    (hCD : C ∩ segment ℝ M D ⊆ {D})
    (hCP : C ∩ segment ℝ M P ⊆ {P}) :
    let K := convexHull ℝ ((C ∩ convexHull ℝ {M,P,D}) ∪ segment ℝ D P)
    IsVisible ℝ K M D ∧ IsVisible ℝ K M P := by
  intro K
  obtain ⟨F,hF⟩ := perpendicular_triangle_coordinates_g2 M (D-M) (P-M)
    (sub_ne_zero.mpr hD) (sub_ne_zero.mpr hP) hperp
  have hF0 : F (0,0) = M := by simp [hF]
  have hF1 : F (1,0) = D := by simp [hF]
  have hF2 : F (0,1) = P := by simp [hF]
  have hFT : F '' convexHull ℝ ({(0,0),(0,1),(1,0)} : Set (ℝ × ℝ)) =
      convexHull ℝ {M,P,D} := by
    change F.toAffineEquiv.toAffineMap '' convexHull ℝ _ = _
    rw [F.toAffineEquiv.toAffineMap.image_convexHull]
    congr 1
    change F '' _ = _
    simp only [image_insert_eq,image_singleton,hF0,hF1,hF2]
  let f : ℂ →ᵃ[ℝ] ℝ := (LinearMap.fst ℝ ℝ ℝ).toAffineMap.comp F.symm.toAffineEquiv.toAffineMap
  let g : ℂ →ᵃ[ℝ] ℝ := (LinearMap.snd ℝ ℝ ℝ).toAffineMap.comp F.symm.toAffineEquiv.toAffineMap
  have hfF (p : ℝ × ℝ) : f (F p)=p.1 := by simp [f]
  have hgF (p : ℝ × ℝ) : g (F p)=p.2 := by simp [g]
  have hf0 : f M=0 := by rw [← hF0,hfF]
  have hfD : f D=1 := by rw [← hF1,hfF]
  have hfP : f P=0 := by rw [← hF2,hfF]
  have hg0 : g M=0 := by rw [← hF0,hgF]
  have hgD : g D=0 := by rw [← hF1,hgF]
  have hgP : g P=1 := by rw [← hF2,hgF]
  have hcoords (x : ℂ) (hx : x ∈ convexHull ℝ {M,P,D}) :
      0 ≤ f x ∧ 0 ≤ g x ∧ f x+g x ≤ 1 := by
    rw [← hFT] at hx
    obtain ⟨p,hp,rfl⟩ := hx
    rw [hfF,hgF]
    rwa [standard_triangle_hull_g2] at hp
  have hgenf : (C ∩ convexHull ℝ {M,P,D}) ∪ segment ℝ D P ⊆
      {x | 0 ≤ f x ∧ (f x=0 → x=P)} := by
    intro x hx
    rcases hx with ⟨hxC,hxT⟩ | hx
    · refine ⟨(hcoords x hxT).1,?_⟩
      intro hfx
      apply hCP
      refine ⟨hxC,?_⟩
      refine ⟨1-g x,g x,sub_nonneg.mpr (by linarith [(hcoords x hxT).2.2]),
        (hcoords x hxT).2.1,by ring,?_⟩
      obtain ⟨p,rfl⟩ := F.surjective x
      have hp1 : p.1=0 := by simpa only [hfF] using hfx
      rw [hgF,hF]
      simp only [hp1,zero_smul,add_zero]
      module
    · obtain ⟨a,b,ha,hb,hab,rfl⟩ := hx
      have he : f (a • D+b • P)=a := by
        rw [Convex.combo_affine_apply (f := f) hab,hfD,hfP]
        simp
      refine ⟨by simpa only [he] using ha,?_⟩
      intro hz
      have ha0 : a=0 := he.symm.trans hz
      have hb1 : b=1 := by linarith
      simp [ha0,hb1]
  have hgeng : (C ∩ convexHull ℝ {M,P,D}) ∪ segment ℝ D P ⊆
      {x | 0 ≤ g x ∧ (g x=0 → x=D)} := by
    intro x hx
    rcases hx with ⟨hxC,hxT⟩ | hx
    · refine ⟨(hcoords x hxT).2.1,?_⟩
      intro hgx
      apply hCD
      refine ⟨hxC,?_⟩
      refine ⟨1-f x,f x,sub_nonneg.mpr (by linarith [(hcoords x hxT).2.2]),
        (hcoords x hxT).1,by ring,?_⟩
      obtain ⟨p,rfl⟩ := F.surjective x
      have hp2 : p.2=0 := by simpa only [hgF] using hgx
      rw [hfF,hF]
      simp only [hp2,zero_smul,add_zero]
      module
    · obtain ⟨a,b,ha,hb,hab,rfl⟩ := hx
      have he : g (a • D+b • P)=b := by
        rw [Convex.combo_affine_apply (f := g) hab,hgD,hgP]
        simp
      refine ⟨by simpa only [he] using hb,?_⟩
      intro hz
      have hb0 : b=0 := he.symm.trans hz
      have ha1 : a=1 := by linarith
      simp [ha1,hb0]
  have hKf := convexHull_min hgenf (convex_affine_nonneg_singleton_fiber_g2 f P)
  have hKg := convexHull_min hgeng (convex_affine_nonneg_singleton_fiber_g2 g D)
  constructor
  · apply (isVisible_iff_lineMap hD.symm).mpr
    intro t ht htx
    have hg : g (AffineMap.lineMap M D t)=0 := by
      rw [AffineMap.apply_lineMap,hg0,hgD]
      simp
    have he := (hKg htx).2 hg
    have hft := congrArg f he
    rw [AffineMap.apply_lineMap,hf0,hfD] at hft
    have ht1 : t=1 := by simpa [AffineMap.lineMap_apply_module] using hft
    exact ht.2.ne ht1
  · apply (isVisible_iff_lineMap hP.symm).mpr
    intro t ht htx
    have hf : f (AffineMap.lineMap M P t)=0 := by
      rw [AffineMap.apply_lineMap,hf0,hfP]
      simp
    have he := (hKf htx).2 hf
    have hgt := congrArg g he
    rw [AffineMap.apply_lineMap,hg0,hgP] at hgt
    have ht1 : t=1 := by simpa [AffineMap.lineMap_apply_module] using hgt
    exact ht.2.ne ht1

/-- Every base point of a nondegenerate perpendicular triangle is visible from
its apex relative to that base. In affine coordinates the coordinate sum is
zero at the apex and one on the base, so a strict radial point has sum less
than one and cannot lie on the base. -/
lemma triangle_base_visible_g2
    (M D P : ℂ) (hD : D ≠ M) (hP : P ≠ M)
    (hperp : (D-M).re*(P-M).re+(D-M).im*(P-M).im=0) :
    ∀ Q ∈ segment ℝ D P, IsVisible ℝ (segment ℝ D P) M Q := by
  obtain ⟨F,hF⟩ := perpendicular_triangle_coordinates_g2 M (D-M) (P-M)
    (sub_ne_zero.mpr hD) (sub_ne_zero.mpr hP) hperp
  let f : ℂ →ᵃ[ℝ] ℝ :=
    ((LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).toAffineMap).comp
      F.symm.toAffineEquiv.toAffineMap
  have hfF (p : ℝ × ℝ) : f (F p)=p.1+p.2 := by simp [f]
  have hF0 : F (0,0)=M := by simp [hF]
  have hF1 : F (1,0)=D := by simp [hF]
  have hF2 : F (0,1)=P := by simp [hF]
  have hf0 : f M=0 := by rw [← hF0,hfF]; norm_num
  have hfD : f D=1 := by rw [← hF1,hfF]; norm_num
  have hfP : f P=1 := by rw [← hF2,hfF]; norm_num
  have hbase : ∀ Q ∈ segment ℝ D P, f Q=1 := by
    rintro Q ⟨a,b,ha,hb,hab,rfl⟩
    rw [Convex.combo_affine_apply (f := f) hab,hfD,hfP]
    simpa only [smul_eq_mul,mul_one] using hab
  intro Q hQ
  have hQM : Q ≠ M := by intro he; have := hbase Q hQ; rw [he,hf0] at this; norm_num at this
  apply (isVisible_iff_lineMap hQM.symm).mpr
  intro t ht htx
  have hft := hbase _ htx
  rw [AffineMap.apply_lineMap,hf0,hbase Q hQ] at hft
  have ht1 : t=1 := by simpa [AffineMap.lineMap_apply_module] using hft
  exact ht.2.ne ht1

end HolomorphicAnosov
