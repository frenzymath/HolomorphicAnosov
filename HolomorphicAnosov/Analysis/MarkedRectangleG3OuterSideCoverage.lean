import HolomorphicAnosov.Analysis.MarkedRectangleG3OuterBoundaryAlignment
import HolomorphicAnosov.Analysis.MarkedRectangleG3BoundarySegmentClosure

open Set
noncomputable section
namespace HolomorphicAnosov.Analysis.MarkedRectangle

/-- On either exterior ray the four-factor boundary derivative points strictly
 downwards. Source: Bak–Newman, Complex Analysis, pp.189–190; there are zero
 or four negative real factors, both giving the same phase `-i`. -/
theorem schwarzChristoffel_outer_integrand_phase (x : Fin 4 → ℝ) {u : ℝ}
    (hout : (∀ j, u < x j) ∨ (∀ j, x j < u)) :
    ∃ r : ℝ, 0 < r ∧
      -Complex.I * (∏ j : Fin 4,
        Complex.exp (-Complex.log ((u : ℂ) - (x j : ℂ)) / 2)) =
          -Complex.I * (r : ℂ) := by
  classical
  have hne (j : Fin 4) : u ≠ x j := by
    rcases hout with h | h
    · exact (h j).ne
    · exact (h j).ne.symm
  have hneC (j : Fin 4) : (u : ℂ) ≠ (x j : ℂ) := by exact_mod_cast hne j
  have hp := (schwarzChristoffel_boundary_branch x).2 u hne
  rw [((schwarzChristoffel_boundary_branch x).1 (u : ℂ) (by simp) hneC).2] at hp
  let r : ℝ := ∏ j : Fin 4, Real.exp (-Real.log |u - x j| / 2)
  refine ⟨r, Finset.prod_pos (fun _ _ ↦ Real.exp_pos _), ?_⟩
  rw [hp]
  have hcast : (∏ j : Fin 4, (Real.exp (-Real.log |u - x j| / 2) : ℂ)) =
      (r : ℂ) := by simp [r]
  rw [hcast]
  rcases hout with h | h
  · have hc : (Finset.univ.filter (fun j : Fin 4 ↦ u < x j)).card = 4 := by simp [h]
    rw [hc]
    norm_num [pow_succ, mul_assoc, Complex.I_mul_I]
  · have hc : (Finset.univ.filter (fun j : Fin 4 ↦ u < x j)).card = 0 := by
      simp [fun j ↦ not_lt.mpr (h j).le]
    rw [hc]
    simp

/-- Boundary increments on either exterior ray have strictly decreasing
imaginary coordinate. Source: Bak–Newman pp.189–190. Multiplication by `i`
turns the derivative into a positive real function, so its integral has strictly
positive real part. -/
theorem schwarzChristoffel_outer_increment_strict (x : Fin 4 → ℝ) {a b : ℝ}
    (hab : a < b) (hout : (∀ j, b < x j) ∨ (∀ j, x j < a))
    (Wbar : ℂ → ℂ)
    (hinc : Wbar (b : ℂ) - Wbar (a : ℂ) = ∫ t in a..b,
      -Complex.I * ∏ j : Fin 4,
        Complex.exp (-Complex.log ((t : ℂ) - (x j : ℂ)) / 2)) :
    (Wbar (b : ℂ)).re = (Wbar (a : ℂ)).re ∧
      (Wbar (b : ℂ)).im < (Wbar (a : ℂ)).im := by
  let f : ℝ → ℂ := fun t ↦ -Complex.I * ∏ j : Fin 4,
    Complex.exp (-Complex.log ((t : ℂ) - (x j : ℂ)) / 2)
  have havoid (j : Fin 4) : x j ∉ Icc a b := by
    intro ht
    rcases hout with h | h
    · exact (h j).not_ge ht.2
    · exact (h j).not_ge ht.1
  have hc : ContinuousOn f (Icc a b) :=
    schwarzChristoffel_integrand_continuousOn_interval x havoid
  have hp : ∀ t ∈ Icc a b, (Complex.I * f t).im = 0 ∧
      0 < (1 : ℝ) * (Complex.I * f t).re := by
    intro t ht
    obtain ⟨r, hr, he⟩ := schwarzChristoffel_outer_integrand_phase x (u := t) (by
      rcases hout with h | h
      · exact Or.inl (fun j ↦ ht.2.trans_lt (h j))
      · exact Or.inr (fun j ↦ (h j).trans_le ht.1))
    change f t = -Complex.I * (r : ℂ) at he
    simp [he, ← mul_assoc, hr]
  have hi : Complex.I * Wbar (b : ℂ) - Complex.I * Wbar (a : ℂ) =
      ∫ t in a..b, Complex.I * f t := by
    rw [← mul_sub, hinc]
    exact (intervalIntegral.integral_const_mul Complex.I f).symm
  simpa only [Complex.mul_im, Complex.mul_re, Complex.I_im, Complex.I_re,
    zero_mul, one_mul, zero_add, zero_sub, neg_lt_neg_iff] using
    signed_horizontal_increment_strict hab (fun t ↦ Complex.I * f t)
      (fun t ↦ Complex.I * Wbar (t : ℂ)) (continuousOn_const.mul hc) hp hi

end HolomorphicAnosov.Analysis.MarkedRectangle


open Set Filter
open scoped _root_.Topology
noncomputable section
namespace HolomorphicAnosov.Analysis.MarkedRectangle

/-- A continuous strictly decreasing ray with finite limit covers the interval
from that limit (excluded) to its endpoint value (included). Source: the exterior
side passage in Bak–Newman, pp.189–190. Extend monotonicity to the finite endpoint,
compare each value to a later value and the limit, then apply the intermediate
value theorem on a sufficiently long finite interval. -/
theorem decreasing_ray_image {a L : ℝ} {f : ℝ → ℝ}
    (hc : ContinuousOn f (Ici a)) (hm : StrictAntiOn f (Ioi a))
    (hlim : Tendsto f atTop (𝓝 L)) :
    StrictAntiOn f (Ici a) ∧ L < f a ∧ f '' Ici a = Ioc L (f a) := by
  have hmclosed : StrictAntiOn f (Ici a) := by
    intro x hx y hy hxy
    have hneg : StrictMonoOn (fun t ↦ -f t) (Icc x y) :=
      strictMonoOn_Icc_of_strictMonoOn_Ioo
        (hc.neg.mono (fun t ht ↦ hx.trans ht.1))
        (fun u hu v hv huv ↦ neg_lt_neg (hm
          (hx.trans_lt hu.1) (hx.trans_lt hv.1) huv))
    exact neg_lt_neg_iff.mp (hneg ⟨le_rfl,hxy.le⟩ ⟨hxy.le,le_rfl⟩ hxy)
  have hbelow (x : ℝ) (hx : x ∈ Ici a) : L < f x := by
    change a ≤ x at hx
    have hxy : f (x+1) < f x := hmclosed hx (by change a ≤ x+1; linarith) (by linarith)
    have hle : L ≤ f (x+1) := by
      apply le_of_tendsto hlim
      filter_upwards [eventually_ge_atTop (x+1)] with t ht
      exact hmclosed.antitoneOn (by change a ≤ x+1; linarith) (by change a ≤ t; linarith) ht
    exact hle.trans_lt hxy
  refine ⟨hmclosed,hbelow a (by simp),Set.Subset.antisymm ?_ ?_⟩
  · rintro v ⟨x,hx,rfl⟩
    exact ⟨hbelow x hx,hmclosed.antitoneOn (by simp) hx hx⟩
  · intro v hv
    have hev : ∀ᶠ t in atTop, f t < v := (tendsto_order.mp hlim).2 v hv.1
    obtain ⟨t,ht,htv⟩ := (eventually_ge_atTop a).and hev |>.exists
    obtain ⟨x,hx,hfx⟩ := intermediate_value_Icc' ht
      (hc.mono (fun x hx ↦ hx.1)) ⟨htv.le,hv.2⟩
    exact ⟨x,hx.1,hfx⟩

/-- The corresponding decreasing left ray includes its finite endpoint and
excludes the common limiting value at minus infinity. Source: Bak–Newman,
pp.189–190. Apply the preceding right-ray result to `-f(-t)`. -/
theorem decreasing_left_ray_image {a L : ℝ} {f : ℝ → ℝ}
    (hc : ContinuousOn f (Iic a)) (hm : StrictAntiOn f (Iio a))
    (hlim : Tendsto f atBot (𝓝 L)) :
    StrictAntiOn f (Iic a) ∧ f a < L ∧ f '' Iic a = Ico (f a) L := by
  have hc' : ContinuousOn (fun t ↦ -f (-t)) (Ici (-a)) :=
    by
      apply ContinuousOn.neg
      apply hc.comp continuous_neg.continuousOn
      intro t ht
      change -t ≤ a
      change -a ≤ t at ht
      linarith
  have hm' : StrictAntiOn (fun t ↦ -f (-t)) (Ioi (-a)) := by
    intro x hx y hy hxy
    exact neg_lt_neg (hm (by simpa only [mem_Iio,mem_Ioi,neg_lt] using hy)
      (by simpa only [mem_Iio,mem_Ioi,neg_lt] using hx) (neg_lt_neg hxy))
  have hl' : Tendsto (fun t ↦ -f (-t)) atTop (𝓝 (-L)) :=
    (hlim.comp tendsto_neg_atTop_atBot).neg
  obtain ⟨hmr,hlr,hir⟩ := decreasing_ray_image hc' hm' hl'
  simp only [neg_neg] at hlr hir
  have hanti : StrictAntiOn f (Iic a) := by
    intro x hx y hy hxy
    have hh := hmr (show -y ∈ Ici (-a) from show -a ≤ -y by exact neg_le_neg hy)
      (show -x ∈ Ici (-a) from show -a ≤ -x by exact neg_le_neg hx) (neg_lt_neg hxy)
    simpa only [neg_neg,neg_lt_neg_iff] using hh
  refine ⟨hanti,by simpa using hlr,Set.Subset.antisymm ?_ ?_⟩
  · rintro v ⟨x,hx,rfl⟩
    have hh : -f x ∈ Ioc (-L) (-f a) := by
      rw [← hir]
      exact ⟨-x,(show -a ≤ -x from neg_le_neg hx),by simp⟩
    exact ⟨by linarith [hh.2],by linarith [hh.1]⟩
  · intro v hv
    have hh : -v ∈ (fun t ↦ -f (-t)) '' Ici (-a) := by
      rw [hir]
      exact ⟨by linarith [hv.2],by linarith [hv.1]⟩
    obtain ⟨t,ht,he⟩ := hh
    exact ⟨-t,(show -t ≤ a from neg_le.mpr ht),by linarith⟩

end HolomorphicAnosov.Analysis.MarkedRectangle

namespace HolomorphicAnosov.Analysis.MarkedRectangle
/-- The exterior rays and their common point at infinity cover exactly the
fourth vertical side. Source: Bak–Newman pp.189–190. Their imaginary coordinates
strictly decrease toward and away from the common limit, while their real
coordinate equals the real part of that limit. The two half-open intervals,
together with the limiting point, form the whole closed side. -/
theorem schwarzChristoffel_outer_side_coverage (x : Fin 4 → ℝ)
    (hx : StrictMono x) (Wbar : ℂ → ℂ) (L : ℂ)
    (hc : Continuous (fun t : ℝ ↦ Wbar (t : ℂ)))
    (htop : Tendsto (fun t : ℝ ↦ Wbar (t : ℂ)) atTop (𝓝 L))
    (hbot : Tendsto (fun t : ℝ ↦ Wbar (t : ℂ)) atBot (𝓝 L))
    (hinc : ∀ a b : ℝ, a ≤ b → (∀ j, x j ∉ Icc a b) →
      Wbar (b : ℂ) - Wbar (a : ℂ) = ∫ t in a..b,
        -Complex.I * ∏ j : Fin 4,
          Complex.exp (-Complex.log ((t : ℂ) - (x j : ℂ)) / 2)) :
    (Wbar (x 0 : ℂ)).im < L.im ∧ L.im < (Wbar (x 3 : ℂ)).im ∧
    (fun t : ℝ ↦ Wbar (t : ℂ)) '' (Iic (x 0) ∪ Ici (x 3)) ∪ {L} =
      Complex.reProdIm {L.re} (Icc (Wbar (x 0 : ℂ)).im (Wbar (x 3 : ℂ)).im) := by
  let f : ℝ → ℝ := fun t ↦ (Wbar (t : ℂ)).im
  have hantiLeft : StrictAntiOn f (Iio (x 0)) := by
    intro a ha b hb hab
    have hbound (j : Fin 4) : b < x j := hb.trans_le (hx.monotone (Fin.zero_le j))
    exact (schwarzChristoffel_outer_increment_strict x hab (Or.inl hbound) Wbar
      (hinc a b hab.le (fun j hj ↦ (hbound j).not_ge hj.2))).2
  have hantiRight : StrictAntiOn f (Ioi (x 3)) := by
    intro a ha b hb hab
    have hbound (j : Fin 4) : x j < a := (hx.monotone (Fin.le_last j)).trans_lt ha
    exact (schwarzChristoffel_outer_increment_strict x hab (Or.inr hbound) Wbar
      (hinc a b hab.le (fun j hj ↦ (hbound j).not_ge hj.1))).2
  have hcf : Continuous f := Complex.continuous_im.comp hc
  obtain ⟨hmleft,hl,hiLeft⟩ := decreasing_left_ray_image hcf.continuousOn hantiLeft
    ((Complex.continuous_im.tendsto L).comp hbot)
  obtain ⟨hmright,hr,hiRight⟩ := decreasing_ray_image hcf.continuousOn hantiRight
    ((Complex.continuous_im.tendsto L).comp htop)
  have hrealLeft : EqOn (fun t : ℝ ↦ (Wbar (t : ℂ)).re) (fun _ ↦ L.re) (Iic (x 0)) := by
    have hopen : EqOn (fun t : ℝ ↦ (Wbar (t : ℂ)).re) (fun _ ↦ L.re) (Iio (x 0)) := by
      intro t ht
      have hevent : (fun u : ℝ ↦ (Wbar (u : ℂ)).re) =ᶠ[atBot]
          (fun _ ↦ (Wbar (t : ℂ)).re) := by
        filter_upwards [eventually_le_atBot t] with u hu
        have hbound (j : Fin 4) : t < x j := ht.trans_le (hx.monotone (Fin.zero_le j))
        exact (schwarzChristoffel_outer_increment_re x hu (Or.inl hbound) Wbar
          (hinc u t hu (fun j hj ↦ (hbound j).not_ge hj.2))).symm
      exact (tendsto_nhds_unique_of_eventuallyEq
        ((Complex.continuous_re.tendsto L).comp hbot) tendsto_const_nhds hevent).symm
    exact hopen.of_subset_closure (Complex.continuous_re.comp hc).continuousOn
      continuousOn_const Iio_subset_Iic_self (by rw [closure_Iio])
  have hrealRight : EqOn (fun t : ℝ ↦ (Wbar (t : ℂ)).re) (fun _ ↦ L.re) (Ici (x 3)) := by
    have hopen : EqOn (fun t : ℝ ↦ (Wbar (t : ℂ)).re) (fun _ ↦ L.re) (Ioi (x 3)) := by
      intro t ht
      have hevent : (fun u : ℝ ↦ (Wbar (u : ℂ)).re) =ᶠ[atTop]
          (fun _ ↦ (Wbar (t : ℂ)).re) := by
        filter_upwards [eventually_ge_atTop t] with u hu
        have hbound (j : Fin 4) : x j < t := (hx.monotone (Fin.le_last j)).trans_lt ht
        exact schwarzChristoffel_outer_increment_re x hu (Or.inr hbound) Wbar
          (hinc t u hu (fun j hj ↦ (hbound j).not_ge hj.1))
      exact (tendsto_nhds_unique_of_eventuallyEq
        ((Complex.continuous_re.tendsto L).comp htop) tendsto_const_nhds hevent).symm
    exact hopen.of_subset_closure (Complex.continuous_re.comp hc).continuousOn
      continuousOn_const Ioi_subset_Ici_self (by rw [closure_Ioi])
  refine ⟨hl,hr,Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    rcases hz with ⟨t,ht,rfl⟩ | rfl
    · rcases ht with ht | ht
      · have hfi : f t ∈ Ico (f (x 0)) L.im := hiLeft ▸ mem_image_of_mem f ht
        exact ⟨hrealLeft ht,hfi.1,hfi.2.le.trans hr.le⟩
      · have hfi : f t ∈ Ioc L.im (f (x 3)) := hiRight ▸ mem_image_of_mem f ht
        exact ⟨hrealRight ht,hl.le.trans hfi.1.le,hfi.2⟩
    · exact ⟨rfl,hl.le,hr.le⟩
  · intro z hz
    rcases lt_trichotomy z.im L.im with hlt | heq | hgt
    · have hfi : z.im ∈ f '' Iic (x 0) := hiLeft.symm ▸ ⟨hz.2.1,hlt⟩
      obtain ⟨t,ht,him⟩ := hfi
      exact Or.inl ⟨t,Or.inl ht,Complex.ext ((hrealLeft ht).trans hz.1.symm) him⟩
    · exact Or.inr (Complex.ext hz.1 heq)
    · have hfi : z.im ∈ f '' Ici (x 3) := hiRight.symm ▸ ⟨hgt,hz.2.2⟩
      obtain ⟨t,ht,him⟩ := hfi
      exact Or.inl ⟨t,Or.inr ht,Complex.ext ((hrealRight ht).trans hz.1.symm) him⟩

end HolomorphicAnosov.Analysis.MarkedRectangle
