import HolomorphicAnosov.Topology.CairnsSixSideRectangleChart
import HolomorphicAnosov.Topology.CairnsAnnulusRectangleFiber
import HolomorphicAnosov.Topology.CairnsAnnulusRectangleRadialSurjective
import HolomorphicAnosov.Topology.GallierXuQuotientDescent
import Mathlib.Tactic.FinCases

noncomputable section
open Set Metric
namespace HolomorphicAnosov.Topology
open GallierXu
private abbrev P : Presentation := [normalWord 0 2]
private abbrev R := sixSideRectangle
private abbrev A := {x : EuclideanSpace ℝ (Fin 2) | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}

private def rectProd (z : R) : Icc (0:ℝ) 1 ×ˢ Icc (1:ℝ) 2 :=
  ⟨(z.val.re,z.val.im), ⟨⟨z.property.1,z.property.2.1⟩,z.property.2.2⟩⟩

private def sideRect (i : Fin 6) (t : ℝ) : ℂ :=
  ![((3-t)/2 : ℝ)*Complex.I, (t:ℂ)+Complex.I,
    1+((3-t)/2 : ℝ)*Complex.I, 1+((3+t)/2 : ℝ)*Complex.I,
    (1-t:ℝ)+2*Complex.I, ((3+t)/2 : ℝ)*Complex.I] i

private lemma chart_side
    (h : Disk ≃ₜ R)
    (hh : ∀ u ∈ Icc (0:ℝ) 6,
      (h ⟨Circle.exp (2*Real.pi*u/6), sphere_subset_closedBall (Circle.exp _).property⟩).val = sixSideRectangleLoop u)
    (i : Fin 6) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    (h (sidePointDisk (P := P) 0 i t)).val = sideRect i t := by
  let u : ℝ := (i.val:ℝ) + if ((P.get 0).get i).2 then t else 1-t
  have hu : u ∈ Icc (0:ℝ) 6 := by
    have hi : (i.val:ℝ) ≤ 5 := by exact_mod_cast (show i.val ≤ 5 by omega)
    have hi0 : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
    dsimp [u]
    split_ifs <;> constructor <;> linarith [ht.1,ht.2]
  have he : (h (sidePointDisk (P := P) 0 i t)).val = sixSideRectangleLoop u := by
    exact hh u hu
  rw [he]
  fin_cases i
  all_goals dsimp [u, P, normalWord, List.range, List.range.loop, List.flatMap, List.get] 
  all_goals norm_num only [Nat.cast_zero, Nat.cast_ofNat, zero_add]
  all_goals apply Complex.ext <;> unfold sideRect sixSideRectangleLoop <;> split_ifs
  all_goals norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im, Complex.normSq]
  all_goals linarith [ht.1, ht.2]

private lemma rectProd_continuous : Continuous rectProd := by
  unfold rectProd
  fun_prop

private lemma rectProd_surjective : Function.Surjective rectProd := by
  intro z
  refine ⟨⟨(z.val.1:ℂ)+z.val.2*Complex.I, ?_⟩, ?_⟩
  · simpa [sixSideRectangle] using And.intro z.property.1.1 (And.intro z.property.1.2 z.property.2)
  · apply Subtype.ext
    simp [rectProd]

private def radial (z : R) : A :=
  ⟨cairns_annulus_rectangle_radial_formula (rectProd z), by
    change 1 ≤ ‖cairns_annulus_rectangle_radial_formula (rectProd z)‖ ∧ ‖cairns_annulus_rectangle_radial_formula (rectProd z)‖ ≤ 2
    rw [radial_norm]
    exact z.property.2.2⟩

private lemma radial_continuous : Continuous radial := by
  unfold radial cairns_annulus_rectangle_radial_formula rectProd
  fun_prop

private lemma radial_surjective : Function.Surjective radial := by
  intro y
  obtain ⟨u,hu⟩ := cairns_annulus_rectangle_radial_formula_surjective y
  obtain ⟨z,hz⟩ := rectProd_surjective u
  exact ⟨z, Subtype.ext (by change cairns_annulus_rectangle_radial_formula (rectProd z) = y.val; rw [hz]; exact hu)⟩

private lemma radial_fiber (z w : R) : radial z = radial w ↔
    z.val.im = w.val.im ∧ (z.val.re = w.val.re ∨
      (z.val.re = 0 ∧ w.val.re = 1) ∨ (z.val.re = 1 ∧ w.val.re = 0)) := by
  rw [Subtype.ext_iff]
  exact cairns_annulus_rectangle_radial_formula_fiber (rectProd z) (rectProd w)

private lemma side_radial_eq
    (h : Disk ≃ₜ R)
    (hh : ∀ u ∈ Icc (0:ℝ) 6,
      (h ⟨Circle.exp (2*Real.pi*u/6), sphere_subset_closedBall (Circle.exp _).property⟩).val = sixSideRectangleLoop u)
    (i j : Fin 6) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
    (hl : ((P.get 0).get i).1 = ((P.get 0).get j).1) :
    radial (h (sidePointDisk (P := P) 0 i t)) = radial (h (sidePointDisk (P := P) 0 j t)) := by
  rw [radial_fiber]
  have hi := chart_side h hh i t ht
  have hj := chart_side h hh j t ht
  rw [hi, hj]
  fin_cases i <;> fin_cases j
  all_goals dsimp [P, normalWord, List.range, List.range.loop, List.flatMap, List.get] at hl
  all_goals norm_num at hl
  all_goals norm_num [sideRect, Complex.mul_re, Complex.mul_im]

private lemma quotient_forward
    (h : Disk ≃ₜ R)
    (hh : ∀ u ∈ Icc (0:ℝ) 6,
      (h ⟨Circle.exp (2*Real.pi*u/6), sphere_subset_closedBall (Circle.exp _).property⟩).val = sixSideRectangleLoop u)
    (x y : FaceDisks P) (hr : Relation.EqvGen (edgeIdentification P) x y) :
    radial (h x.2) = radial (h y.2) := by
  induction hr with
  | rel x y hxy =>
    rcases x with ⟨f,x⟩
    rcases y with ⟨g,y⟩
    have hf : f = 0 := Fin.ext (by change f.val = 0; have hf := f.isLt; change f.val < 1 at hf; omega)
    have hg : g = 0 := Fin.ext (by change g.val = 0; have hg := g.isLt; change g.val < 1 at hg; omega)
    subst f; subst g
    obtain ⟨i,j,t,ht,hl,hx,hy⟩ := hxy
    have hx' : x = sidePointDisk (P := P) 0 i t := Subtype.ext hx
    have hy' : y = sidePointDisk (P := P) 0 j t := Subtype.ext hy
    simpa only [hx', hy'] using side_radial_eq h hh i j t ht hl
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih ij => exact ih.trans ij

private lemma seam_related
    (h : Disk ≃ₜ R)
    (hh : ∀ u ∈ Icc (0:ℝ) 6,
      (h ⟨Circle.exp (2*Real.pi*u/6), sphere_subset_closedBall (Circle.exp _).property⟩).val = sixSideRectangleLoop u)
    (x y : Disk) (hx : (h x).val.re = 0) (hy : (h y).val.re = 1)
    (hr : (h x).val.im = (h y).val.im) :
    Relation.EqvGen (edgeIdentification P) (0,x) (0,y) := by
  let r := (h x).val.im
  have hb : 1 ≤ r ∧ r ≤ 2 := (h x).property.2.2
  have hpoint (z : Disk) (i : Fin 6) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
      (hz : (h z).val = sideRect i t) : z.val = sidePoint P 0 i t := by
    have he : z = sidePointDisk (P := P) 0 i t :=
      h.injective (Subtype.ext (hz.trans (chart_side h hh i t ht).symm))
    exact congrArg Subtype.val he
  by_cases hm : r ≤ 3/2
  · let t := 3-2*r
    have ht : t ∈ Icc (0:ℝ) 1 := ⟨by dsimp [t]; linarith, by dsimp [t]; linarith [hb.1]⟩
    apply Relation.EqvGen.rel
    refine ⟨(0:Fin 6),(2:Fin 6),t,ht,by rfl,?_,?_⟩
    · apply hpoint x 0 t ht
      apply Complex.ext
      · simpa [sideRect] using hx
      · simp [sideRect, t, r]
    · apply hpoint y 2 t ht
      apply Complex.ext
      · simpa [sideRect] using hy
      · simp [sideRect,t]
        dsimp [r]
        linarith
  · let t := 2*r-3
    have ht : t ∈ Icc (0:ℝ) 1 := ⟨by dsimp [t]; linarith, by dsimp [t]; linarith [hb.2]⟩
    apply Relation.EqvGen.rel
    refine ⟨(5:Fin 6),(3:Fin 6),t,ht,by rfl,?_,?_⟩
    · apply hpoint x 5 t ht
      apply Complex.ext
      · simpa [sideRect] using hx
      · simp [sideRect,t,r]
    · apply hpoint y 3 t ht
      apply Complex.ext
      · simpa [sideRect] using hy
      · simp [sideRect,t]
        dsimp [r]
        linarith

private lemma quotient_reverse
    (h : Disk ≃ₜ R)
    (hh : ∀ u ∈ Icc (0:ℝ) 6,
      (h ⟨Circle.exp (2*Real.pi*u/6), sphere_subset_closedBall (Circle.exp _).property⟩).val = sixSideRectangleLoop u)
    (x y : FaceDisks P) (he : radial (h x.2) = radial (h y.2)) :
    Relation.EqvGen (edgeIdentification P) x y := by
  rcases x with ⟨f,x⟩
  rcases y with ⟨g,y⟩
  have hf : f = 0 := Fin.ext (by change f.val = 0; have hf := f.isLt; change f.val < 1 at hf; omega)
  have hg : g = 0 := Fin.ext (by change g.val = 0; have hg := g.isLt; change g.val < 1 at hg; omega)
  subst f; subst g
  obtain ⟨hr,he | he | he⟩ := (radial_fiber (h x) (h y)).mp he
  · have hxy : x = y := h.injective (Subtype.ext (Complex.ext he hr))
    subst y
    exact Relation.EqvGen.refl _
  · exact seam_related h hh x y he.1 he.2 hr
  · exact Relation.EqvGen.symm _ _ (seam_related h hh y x he.2 he.1 hr.symm)

private lemma boundary_representative
    (h : Disk ≃ₜ R)
    (hh : ∀ u ∈ Icc (0:ℝ) 6,
      (h ⟨Circle.exp (2*Real.pi*u/6), sphere_subset_closedBall (Circle.exp _).property⟩).val = sixSideRectangleLoop u)
    (a : ℕ) (ha : a = 1 ∨ a = 3) (d : Disk) :
    (∃ i : Fin 6, ∃ t ∈ Icc (0:ℝ) 1, ((P.get 0).get i).1 = a ∧
      d.val = sidePoint P 0 i t) ↔ (h d).val.im = (if a = 1 then 1 else 2) := by
  constructor
  · rintro ⟨i,t,ht,hl,hd⟩
    have hd' : d = sidePointDisk (P := P) 0 i t := Subtype.ext hd
    rw [hd']
    have hs := chart_side h hh i t ht
    rw [hs]
    rcases ha with rfl | rfl <;> fin_cases i
    all_goals dsimp [P, normalWord, List.range, List.range.loop, List.flatMap, List.get] at hl
    all_goals norm_num at hl
    all_goals norm_num [sideRect]
  · intro hd
    rcases ha with rfl | rfl
    · let t := (h d).val.re
      have ht : t ∈ Icc (0:ℝ) 1 := ⟨(h d).property.1,(h d).property.2.1⟩
      refine ⟨1,t,ht,by rfl,?_⟩
      have he : d = sidePointDisk (P := P) 0 (1:Fin 6) t := by
        apply h.injective
        apply Subtype.ext
        rw [chart_side h hh 1 t ht]
        apply Complex.ext <;> simp [sideRect,t]; simpa using hd
      exact congrArg Subtype.val he
    · let t := 1-(h d).val.re
      have ht : t ∈ Icc (0:ℝ) 1 := ⟨by dsimp [t]; linarith [(h d).property.2.1], by dsimp [t]; linarith [(h d).property.1]⟩
      refine ⟨4,t,ht,by rfl,?_⟩
      have he : d = sidePointDisk (P := P) 0 (4:Fin 6) t := by
        apply h.injective
        apply Subtype.ext
        rw [chart_side h hh 4 t ht]
        apply Complex.ext <;> simp [sideRect,t]; simpa using hd
      exact congrArg Subtype.val he

/-- The genus-zero two-boundary polygon is the rectangle with its equal-height
vertical sides identified. The prescribed disk chart matches each occurrence,
the radial map has exactly the generated edge fibres, and compact quotient
descent gives the homeomorphism. The unpaired labels 1 and 3 have radii 1 and 2.
Source: Gallier–Xu, Proposition 3.2 and Lemma 6.1; Cairns (1951), §2(B), p.860. -/
theorem cairns_polygonal_annulus_normal_word_cylinder
    {g : ℕ} (hg : g = 0) :
    ∃ T : Realization [normalWord g 2] ≃ₜ
        {x : EuclideanSpace ℝ (Fin 2) | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
      T '' edgeImage [normalWord g 2] (2 * g + 1) =
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
      T '' edgeImage [normalWord g 2] (2 * g + 3) =
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 2 := by
  subst g
  obtain ⟨h,hh⟩ := sixSideRectangle_disk_parameter
  let q : FaceDisks P → A := fun x => radial (h x.2)
  have hq : Continuous q := radial_continuous.comp (h.continuous.comp continuous_snd)
  have hsurj : Function.Surjective q := by
    intro z
    obtain ⟨r,hr⟩ := radial_surjective z
    exact ⟨(0,h.symm r),by simpa [q] using hr⟩
  obtain ⟨H,hH⟩ := realization_homeomorph_of_fibres q hq hsurj
    (fun x y => ⟨quotient_reverse h hh x y,quotient_forward h hh x y⟩)
  let T := H.symm
  have hT (x : FaceDisks P) : T (project P x) = q x := by
    rw [← hH]
    exact H.symm_apply_apply _
  have hnorm (x : FaceDisks P) : ‖(T (project P x)).val‖ = (h x.2).val.im := by
    rw [hT]
    exact radial_norm _
  have hb (a : ℕ) (ha : a = 1 ∨ a = 3) :
      (fun x : Realization P => (T x).val) '' edgeImage P a =
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) (if a = 1 then 1 else 2) := by
    ext z
    constructor
    · rintro ⟨v,⟨x,i,t,ht,hl,hx,rfl⟩,rfl⟩
      rw [mem_sphere_zero_iff_norm, hnorm]
      rcases x with ⟨f,d⟩
      have hf : f = 0 := Fin.ext (by change f.val = 0; have hf := f.isLt; change f.val < 1 at hf; omega)
      subst f
      exact (boundary_representative h hh a ha d).mp ⟨i,t,ht,hl,hx⟩
    · intro hz
      have hz' : 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 := by
        rw [mem_sphere_zero_iff_norm] at hz
        rcases ha with rfl | rfl <;> norm_num at hz <;> constructor <;> linarith
      let w : A := ⟨z,hz'⟩
      obtain ⟨x,hx⟩ := hsurj w
      refine ⟨project P x, ?_, ?_⟩
      · rcases x with ⟨f,d⟩
        have hf : f = 0 := Fin.ext (by change f.val = 0; have hf := f.isLt; change f.val < 1 at hf; omega)
        subst f
        have hn : (h d).val.im = (if a = 1 then 1 else 2) := by
          rw [← hnorm (0,d), hT, hx]
          exact mem_sphere_zero_iff_norm.mp hz
        obtain ⟨i,t,ht,hl,hd⟩ := (boundary_representative h hh a ha d).mpr hn
        exact ⟨(0,d),i,t,ht,hl,hd,rfl⟩
      · change (T (project P x)).val = z
        rw [hT,hx]
  refine ⟨T, ?_, ?_⟩
  · simpa [Set.image_image, P] using hb 1 (Or.inl rfl)
  · simpa [Set.image_image, P] using hb 3 (Or.inr rfl)

end HolomorphicAnosov.Topology

