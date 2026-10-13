import HolomorphicAnosov.Topology.CompactTriangleRadialGraphG2
import HolomorphicAnosov.Topology.PerpendicularTriangleCoordinatesG2
import Mathlib.Analysis.Convex.Join

open Set
namespace HolomorphicAnosov

lemma standard_triangle_hull_g2 :
    convexHull ℝ ({(0,0),(0,1),(1,0)} : Set (ℝ × ℝ)) =
      {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1+p.2 ≤ 1} := by
  apply Subset.antisymm
  · apply convexHull_min
    · rintro p (rfl | rfl | rfl) <;> norm_num
    · intro p hp q hq a b ha hb hab
      simp only [Prod.smul_fst,Prod.smul_snd,Prod.fst_add,Prod.snd_add,smul_eq_mul,mem_ofPred_eq]
      refine ⟨add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1),
        add_nonneg (mul_nonneg ha hp.2.1) (mul_nonneg hb hq.2.1),?_⟩
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hp.2.2),mul_nonneg hb (sub_nonneg.mpr hq.2.2)]
  · intro p hp
    rw [convexHull_insert (insert_nonempty (0,1) {(1,0)}),convexHull_pair,mem_convexJoin]
    by_cases hzero : p.1+p.2=0
    · have hp0 : p=(0,0) := Prod.ext (by linarith [hp.1,hp.2.1]) (by linarith [hp.1,hp.2.1])
      subst p
      exact ⟨(0,0),rfl,(0,1),left_mem_segment ℝ _ _,left_mem_segment ℝ _ _⟩
    have hs : 0 < p.1+p.2 := lt_of_le_of_ne (add_nonneg hp.1 hp.2.1) (Ne.symm hzero)
    refine ⟨(0,0),rfl,(p.1/(p.1+p.2),p.2/(p.1+p.2)),?_,?_⟩
    · refine ⟨p.2/(p.1+p.2),p.1/(p.1+p.2),div_nonneg hp.2.1 hs.le,div_nonneg hp.1 hs.le,?_,?_⟩
      · rw [← add_div,add_comm p.2 p.1,div_self hzero]
      · ext <;> simp
    · refine ⟨1-(p.1+p.2),p.1+p.2,sub_nonneg.mpr hp.2.2,hs.le,by ring,?_⟩
      ext <;> simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mul_zero,zero_add] <;> field_simp

lemma affineEquiv_visible_image_g2 {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : E ≃ᵃ[ℝ] F) (K : Set E) (x y : E) :
    IsVisible ℝ (f '' K) (f x) (f y) ↔ IsVisible ℝ K x y := by
  constructor
  · intro h z hz hzxy
    exact h ⟨z,hz,rfl⟩ ((f.sbtw_map_iff).mpr hzxy)
  · rintro h _ ⟨z,hz,rfl⟩ hzxy
    exact h hz ((f.sbtw_map_iff).mp hzxy)

/-- The visible part of a compact convex hull in a nondegenerate right triangle
is compact. Source: Cairns (1951), §3 Case II, p.863. Use perpendicular affine
coordinates and the continuous radial graph theorem for the standard triangle;
the visible set is the continuous image of the compact unit interval. -/
theorem halfSector_visible_compact_g2 (M D P : ℂ) (hD : D ≠ M) (hP : P ≠ M)
    (hperp : (D-M).re*(P-M).re+(D-M).im*(P-M).im=0)
    (K : Set ℂ) (hK : IsCompact K) (hconv : Convex ℝ K) (hM : M ∉ K)
    (hbase : segment ℝ D P ⊆ K) (htri : K ⊆ convexHull ℝ {M,P,D}) :
    IsCompact {Q ∈ K | IsVisible ℝ K M Q} := by
  obtain ⟨F,hF⟩ := perpendicular_triangle_coordinates_g2 M (D-M) (P-M)
    (sub_ne_zero.mpr hD) (sub_ne_zero.mpr hP) hperp
  have hF0 : F (0,0) = M := by simp [hF]
  have hF1 : F (1,0) = D := by simp [hF]
  have hF2 : F (0,1) = P := by simp [hF]
  let K' : Set (ℝ × ℝ) := F ⁻¹' K
  have hK' : IsCompact K' := F.toHomeomorph.isCompact_preimage.mpr hK
  have hc' : Convex ℝ K' := hconv.affine_preimage F.toAffineEquiv.toAffineMap
  have hT : ∀ p ∈ K', 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1+p.2 ≤ 1 := by
    intro p hp
    have hFtri : F '' convexHull ℝ ({(0,0),(0,1),(1,0)} : Set (ℝ × ℝ)) =
        convexHull ℝ {M,P,D} := by
      change F.toAffineEquiv.toAffineMap '' convexHull ℝ _ = _
      rw [F.toAffineEquiv.toAffineMap.image_convexHull]
      simpa only [image_insert_eq,image_singleton] using
        congrArg (convexHull ℝ) (show F.toAffineEquiv.toAffineMap '' {(0,0),(0,1),(1,0)} = {M,P,D} by
          change F '' _ = _
          simp only [image_insert_eq,image_singleton,hF0,hF1,hF2])
    have hmem := htri hp
    rw [← hFtri] at hmem
    obtain ⟨q,hq,hqp⟩ := hmem
    have hqp' : q=p := F.injective hqp
    subst q
    rwa [standard_triangle_hull_g2] at hq
  have hz' : (0 : ℝ × ℝ) ∉ K' := by
    intro hz
    exact hM (hF0 ▸ hz)
  have hb' (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : (s,1-s) ∈ K' := by
    apply hbase
    refine ⟨s,1-s,hs.1,sub_nonneg.mpr hs.2,by ring,?_⟩
    rw [hF]
    module
  obtain ⟨H,hHc,_,hH1,hgraph⟩ := compact_triangle_radial_graph_g2 K' hK' hc' hT hz' hb'
  have hcont : ContinuousOn (fun s ↦ (s/H s,(1-s)/H s)) (Icc (0:ℝ) 1) := by
    have hn : ∀ s ∈ Icc (0:ℝ) 1, H s ≠ 0 := fun s hs ↦
      (lt_of_lt_of_le zero_lt_one (hH1 s hs)).ne'
    exact (continuousOn_id.div hHc hn).prodMk
      ((continuousOn_const.sub continuousOn_id).div hHc hn)
  have hVcompact : IsCompact {p ∈ K' | IsVisible ℝ K' 0 p} := by
    rw [hgraph]
    exact isCompact_Icc.image_of_continuousOn hcont
  have hFK : F '' K' = K := F.surjective.image_preimage K
  have himage : F '' {p ∈ K' | IsVisible ℝ K' 0 p} = {q ∈ K | IsVisible ℝ K M q} := by
    ext q
    constructor
    · rintro ⟨p,⟨hp,hpv⟩,rfl⟩
      refine ⟨hp,?_⟩
      rw [← hFK,← hF0]
      exact (affineEquiv_visible_image_g2 F.toAffineEquiv K' 0 p).mpr hpv
    · rintro ⟨hq,hqv⟩
      obtain ⟨p,rfl⟩ := F.surjective q
      refine ⟨p,⟨hq,?_⟩,rfl⟩
      apply (affineEquiv_visible_image_g2 F.toAffineEquiv K' 0 p).mp
      change IsVisible ℝ (F '' K') (F (0,0)) (F p)
      simpa only [hFK,hF0] using hqv
  rw [← himage]
  exact hVcompact.image F.continuous

end HolomorphicAnosov
