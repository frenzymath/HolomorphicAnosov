import HolomorphicAnosov.Topology.CompactConvexUpperFrontG2
import HolomorphicAnosov.Topology.PositivePerspectiveConvexG2
import Mathlib.Analysis.Convex.Visible

open Set Filter Topology

namespace HolomorphicAnosov

/-- The affine coordinate change from triangle coordinates to perspective coordinates. -/
def triangleShearG2 : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (p.1, p.1 + p.2)
  map_add' p q := by (ext <;> simp); ring
  map_smul' a p := by (ext <;> simp); ring

/-- A compact convex subset of the standard triangle containing its opposite base
and omitting the apex has a continuous radial front.

Source: Cairns (1951), §3 Case II, p.863, expanded by the positive perspective
construction of Boyd–Vandenberghe §2.3.3, pp.39–42. Send (u,v) to
(u/(u+v),1/(u+v)). The image is compact and convex and projects onto [0,1].
Its continuous concave upper boundary H satisfies H≥1. The inverse transform
sends that graph to R(s)=(s/H(s),(1-s)/H(s)). On each ray, larger perspective
height means smaller radius. Consequently these are exactly the points visible
from the origin in the original convex set. -/
theorem compact_triangle_radial_graph_g2 (K : Set (ℝ × ℝ))
    (hK : IsCompact K) (hconv : Convex ℝ K)
    (htri : ∀ p ∈ K, 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1)
    (hzero : (0 : ℝ × ℝ) ∉ K)
    (hbase : ∀ s ∈ Icc (0 : ℝ) 1, (s,1-s) ∈ K) :
    ∃ H : ℝ → ℝ, ContinuousOn H (Icc 0 1) ∧ ConcaveOn ℝ (Icc 0 1) H ∧
      (∀ s ∈ Icc (0 : ℝ) 1, 1 ≤ H s) ∧
      {p ∈ K | IsVisible ℝ K 0 p} =
        (fun s ↦ (s / H s, (1-s) / H s)) '' Icc (0 : ℝ) 1 := by
  have hσ (p : ℝ × ℝ) (hp : p ∈ K) : 0 < p.1+p.2 := by
    obtain ⟨hx,hy,_⟩ := htri p hp
    by_contra hn
    have hsum : p.1+p.2 ≤ 0 := not_lt.mp hn
    have hx0 : p.1 = 0 := by linarith
    have hy0 : p.2 = 0 := by linarith
    exact hzero ((show p = 0 from Prod.ext hx0 hy0) ▸ hp)
  let T : ℝ × ℝ → ℝ × ℝ := fun p ↦ positivePerspectiveG2 (triangleShearG2 p)
  have hT : ContinuousOn T K :=
    positivePerspectiveG2_continuousOn.comp
      triangleShearG2.continuous_of_finiteDimensional.continuousOn
      (fun p hp ↦ hσ p hp)
  have himgK : IsCompact (T '' K) := hK.image_of_continuousOn hT
  have himgconv : Convex ℝ (T '' K) := by
    rw [show T '' K = positivePerspectiveG2 '' (triangleShearG2 '' K) by
      exact (image_image _ _ _).symm]
    apply positivePerspectiveG2_convex_image (hconv.linear_image triangleShearG2)
    rintro _ ⟨p,hp,rfl⟩
    exact hσ p hp
  have hproj : Prod.fst '' (T '' K) = Icc (0 : ℝ) 1 := by
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨p,hp,rfl⟩, rfl⟩
      change p.1/(p.1+p.2) ∈ Icc (0:ℝ) 1
      exact ⟨div_nonneg (htri p hp).1 (hσ p hp).le,
        (div_le_one (hσ p hp)).mpr (by linarith [(htri p hp).2.1])⟩
    · intro s hs
      refine ⟨(s,1), ?_, rfl⟩
      refine ⟨(s,1-s), hbase s hs, ?_⟩
      simp [T, positivePerspectiveG2, triangleShearG2]
  obtain ⟨H,hHc,hHconc,hH⟩ := compact_convex_upper_front_g2 _ himgK himgconv hproj
  have hH1 (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : 1 ≤ H s := by
    apply (hH s hs).2 1
    exact ⟨(s,1-s),hbase s hs,by simp [T,positivePerspectiveG2,triangleShearG2]⟩
  have hHpos (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : 0 < H s := lt_of_lt_of_le zero_lt_one (hH1 s hs)
  let R : ℝ → ℝ × ℝ := fun s ↦ (s/H s,(1-s)/H s)
  have hR (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : R s ∈ K := by
    obtain ⟨p,hp,he⟩ := (hH s hs).1
    have he1 : p.1/(p.1+p.2)=s := congrArg Prod.fst he
    have he2 : 1/(p.1+p.2)=H s := congrArg Prod.snd he
    have hrp : R s = p := by
      apply Prod.ext <;> dsimp [R]
      · rw [← he2,← he1]; field_simp [(hσ p hp).ne']
      · rw [← he2,← he1]; field_simp [(hσ p hp).ne']; ring
    rwa [hrp]
  have hRsigma (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : (R s).1+(R s).2 = 1/H s := by
    dsimp [R]; ring
  have hRvis (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : IsVisible ℝ K 0 (R s) := by
    have hR0 : (0 : ℝ × ℝ) ≠ R s := fun he ↦ hzero (he ▸ hR s hs)
    apply (isVisible_iff_lineMap hR0).mpr
    intro t ht htp
    have htp' : (t*(s/H s),t*((1-s)/H s)) ∈ K := by
      simpa [AffineMap.lineMap_apply_module,R] using htp
    have hTpoint : (s,H s/t) ∈ T '' K := by
      refine ⟨_,htp',?_⟩
      apply Prod.ext <;> dsimp [T,positivePerspectiveG2,triangleShearG2]
      · field_simp [ht.1.ne', (hHpos s hs).ne']; ring
      · field_simp [ht.1.ne', (hHpos s hs).ne']; ring
    have hmax := (hH s hs).2 _ hTpoint
    have hless : H s < H s/t := (lt_div_iff₀ ht.1).mpr
      (mul_lt_of_lt_one_right (hHpos s hs) ht.2)
    exact hless.not_ge hmax
  refine ⟨H,hHc,hHconc,hH1,?_⟩
  apply Subset.antisymm
  · rintro p ⟨hp,hpvis⟩
    let s := p.1/(p.1+p.2)
    have hs : s ∈ Icc (0:ℝ) 1 := by
      rw [← hproj]
      exact ⟨T p,⟨p,hp,rfl⟩,rfl⟩
    have hmax : 1/(p.1+p.2) ≤ H s := (hH s hs).2 _ ⟨p,hp,rfl⟩
    have he : 1/(p.1+p.2) = H s := by
      by_contra hn
      have hlt := lt_of_le_of_ne hmax hn
      let t := 1 / ((p.1+p.2)*H s)
      have ht0 : 0 < t := one_div_pos.mpr (mul_pos (hσ p hp) (hHpos s hs))
      have ht1 : t < 1 := by
        dsimp [t]
        apply (div_lt_one (mul_pos (hσ p hp) (hHpos s hs))).mpr
        exact (div_lt_iff₀ (hσ p hp)).mp hlt |>.trans_eq (mul_comm _ _)
      have heR : AffineMap.lineMap (0 : ℝ × ℝ) p t = R s := by
        simp only [AffineMap.lineMap_apply_module, smul_zero, zero_add]
        apply Prod.ext <;> dsimp [R,t,s]
        · field_simp [(hσ p hp).ne', (hHpos s hs).ne']
        · field_simp [(hσ p hp).ne', (hHpos s hs).ne']; ring
      exact (isVisible_iff_lineMap (ne_of_mem_of_not_mem hp hzero).symm).mp hpvis
        t ⟨ht0,ht1⟩ (heR ▸ hR s hs)
    refine ⟨s,hs,?_⟩
    apply Prod.ext <;> dsimp [R]
    · rw [← he]; dsimp [s]; field_simp [(hσ p hp).ne']
    · rw [← he]; dsimp [s]; field_simp [(hσ p hp).ne']; ring
  · rintro p ⟨s,hs,rfl⟩
    exact ⟨hR s hs,hRvis s hs⟩

end HolomorphicAnosov
