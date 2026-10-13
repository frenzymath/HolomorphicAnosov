import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic

open Set
namespace HolomorphicAnosov

lemma complex_linear_functional_second_coordinate_g2 (f : ℂ →L[ℝ] ℝ) (hf : f ≠ 0) :
    ∃ g : ℂ →L[ℝ] ℝ, ∀ x y, f x=f y → g x=g y → x=y := by
  have hformula (z : ℂ) : f z=z.re*f 1+z.im*f Complex.I := by
    have hz : z=z.re • (1:ℂ)+z.im • Complex.I := by apply Complex.ext <;> simp
    calc
      f z = f (z.re • (1:ℂ)+z.im • Complex.I) := congrArg f hz
      _ = _ := by simp only [map_add,map_smul,smul_eq_mul]
  by_cases hI : f Complex.I=0
  · have h1 : f 1 ≠ 0 := by
      intro h1
      apply hf
      ext z
      simp [hformula z,hI,h1]
    refine ⟨Complex.imCLM,?_⟩
    intro x y hxy hg
    have hre : x.re=y.re := by
      apply mul_right_cancel₀ h1
      simpa only [hformula x,hformula y,hI,mul_zero,add_zero] using hxy
    exact Complex.ext hre hg
  · refine ⟨Complex.reCLM,?_⟩
    intro x y hxy hg
    have him : x.im=y.im := by
      apply mul_right_cancel₀ hI
      rw [hformula x,hformula y] at hxy
      change x.re=y.re at hg
      rw [hg] at hxy
      linarith
    exact Complex.ext hg him

lemma supporting_face_min_extreme_g2
    (K : Set ℂ) (f g : ℂ →L[ℝ] ℝ) (c : ℝ)
    (hinj : ∀ x y, f x=f y → g x=g y → x=y)
    (hbound : ∀ x ∈ K, f x ≤ c)
    {A : ℂ} (hA : A ∈ K) (hfA : f A=c)
    (hmin : ∀ x ∈ K, f x=c → g A ≤ g x) : A ∈ K.extremePoints ℝ := by
  rw [mem_extremePoints]
  refine ⟨hA,?_⟩
  rintro x hx y hy ⟨a,b,ha,hb,hab,he⟩
  have hfe : a*f x+b*f y=c := by simpa only [map_add,map_smul,smul_eq_mul,hfA] using congrArg f he
  have hsumf : (a+b)*c=c := by rw [hab,one_mul]
  have hfx : f x=c := by
    have hprod := mul_nonneg hb.le (sub_nonneg.mpr (hbound y hy))
    have hz : a*(c-f x)=0 := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr (hbound x hx))]
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ha.ne')).symm
  have hfy : f y=c := by
    have hprod := mul_nonneg ha.le (sub_nonneg.mpr (hbound x hx))
    have hz : b*(c-f y)=0 := by nlinarith [mul_nonneg hb.le (sub_nonneg.mpr (hbound y hy))]
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hb.ne')).symm
  have hge : a*g x+b*g y=g A := by simpa only [map_add,map_smul,smul_eq_mul] using congrArg g he
  have hsumg : (a+b)*g A=g A := by rw [hab,one_mul]
  have hgx : g x=g A := by
    have hprod := mul_nonneg hb.le (sub_nonneg.mpr (hmin y hy hfy))
    have hz : a*(g x-g A)=0 := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr (hmin x hx hfx))]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ha.ne')
  have hgy : g y=g A := by
    have hprod := mul_nonneg ha.le (sub_nonneg.mpr (hmin x hx hfx))
    have hz : b*(g y-g A)=0 := by nlinarith [mul_nonneg hb.le (sub_nonneg.mpr (hmin y hy hfy))]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hb.ne')
  exact ⟨hinj x A (hfx.trans hfA.symm) hgx,hinj y A (hfy.trans hfA.symm) hgy⟩

/-- A nonempty supporting face of a compact convex planar set is the closed
segment joining two extreme points of the set.

Source: Rockafellar, Convex Analysis (1970), §18, Theorems 18.1 and 18.3,
pp.163–165. This is an explicit two-dimensional expansion. Complete a nonzero
supporting functional f to injective real coordinates (f,g). On the compact
face f=c, attain the minimum and maximum of g at A,B. Every intermediate g-value
is represented by a convex combination of A,B, and injectivity of (f,g) shows
that this combination is the given face point. If an endpoint is a strict
convex combination of points of K, the supporting inequality forces both into
the same face; extremality of its g-value then forces both points to coincide
with that endpoint. -/
theorem planar_supporting_face_segment_g2
    (K : Set ℂ) (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : ℂ →L[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hbound : ∀ x ∈ K, f x ≤ c) (hne : {x ∈ K | f x=c}.Nonempty) :
    ∃ A B : ℂ, A ∈ K.extremePoints ℝ ∧ B ∈ K.extremePoints ℝ ∧
      {x ∈ K | f x=c} = segment ℝ A B := by
  obtain ⟨g,hinj⟩ := complex_linear_functional_second_coordinate_g2 f hf
  let C : Set ℂ := {x ∈ K | f x=c}
  have hC : IsCompact C := hK.inter_right (isClosed_eq f.continuous continuous_const)
  obtain ⟨A,hA,hmin⟩ := hC.exists_isMinOn hne g.continuous.continuousOn
  obtain ⟨B,hB,hmax⟩ := hC.exists_isMaxOn hne g.continuous.continuousOn
  have hAext : A ∈ K.extremePoints ℝ := supporting_face_min_extreme_g2 K f g c hinj hbound
    hA.1 hA.2 (fun x hx hfx ↦ hmin ⟨hx,hfx⟩)
  have hBext : B ∈ K.extremePoints ℝ := by
    apply supporting_face_min_extreme_g2 K f (-g) c
      (fun x y hfx hgx ↦ hinj x y hfx (neg_injective hgx)) hbound hB.1 hB.2
    intro x hx hfx
    exact neg_le_neg (hmax ⟨hx,hfx⟩)
  refine ⟨A,B,hAext,hBext,?_⟩
  apply Subset.antisymm
  · intro x hx
    by_cases he : g A=g B
    · have hxA : x=A := hinj x A (hx.2.trans hA.2.symm)
        (by have hl : g A ≤ g x := hmin hx; have hu : g x ≤ g B := hmax hx; linarith)
      exact hxA.symm ▸ left_mem_segment ℝ A B
    have hlt : g A<g B := lt_of_le_of_ne (hmin hB) he
    let t : ℝ := (g x-g A)/(g B-g A)
    have hd : 0 < g B-g A := sub_pos.mpr hlt
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr (hmin hx)) hd.le
    have ht1 : t ≤ 1 := (div_le_one hd).mpr (by have hu : g x ≤ g B := hmax hx; linarith)
    refine ⟨1-t,t,sub_nonneg.mpr ht1,ht0,by ring,?_⟩
    apply hinj
    · simp only [map_add,map_smul,smul_eq_mul,hA.2,hB.2,hx.2]
      ring
    · simp only [map_add,map_smul,smul_eq_mul]
      dsimp [t]
      field_simp [hd.ne']
      ring
  · intro x hx
    refine ⟨hconv.segment_subset hA.1 hB.1 hx,?_⟩
    obtain ⟨a,b,ha,hb,hab,rfl⟩ := hx
    simp only [map_add,map_smul,smul_eq_mul,hA.2,hB.2]
    rw [← add_mul,hab,one_mul]

end HolomorphicAnosov
