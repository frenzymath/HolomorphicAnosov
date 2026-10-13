import HolomorphicAnosov.Topology.CairnsSimplePolygonSchoenflies
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Directed-circle arcs crossing radial polygon edges

DAG node: `topo.circle_radial_edge_crossing_g20`.
Source: Cairns (1951), Lemma 5.1, printed p.866, circle-arc crossing step.
The arc uses Mathlib's positive angular difference. Its determinant at a radial
edge is computed explicitly, and markers are selected by connectedness of the
open directed arcs in the twice-punctured circle.
-/

open Set Metric
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace HolomorphicAnosov

/-- The affine angular parametrization of the directed circle arc, extended to
all real parameters. Source: Cairns (1951), Lemma 5.1 p.866. -/
def circleAngularArc (u v : Circle) (t : ℝ) : ℂ :=
  Circle.exp (t * Circle.angleDiff u v) * u

lemma circleAngularArc_path (u v : Circle) (t : unitInterval) :
    circleAngularArc u v t = (Circle.path u v t : ℂ) := by
  rw [Circle.path_apply, Path.segment_apply, AffineMap.lineMap_apply_module]
  simp only [smul_eq_mul]
  change ((Circle.exp ((t : ℝ) * Circle.angleDiff u v) * u : Circle) : ℂ) =
    (Circle.exp ((1 - (t : ℝ)) * (u : ℂ).arg + (t : ℝ) *
      (Circle.angleDiff u v + (u : ℂ).arg)) : ℂ)
  congr 1
  rw [show (1 - (t : ℝ)) * (u : ℂ).arg + (t : ℝ) *
      (Circle.angleDiff u v + (u : ℂ).arg) =
      (t : ℝ) * Circle.angleDiff u v + (u : ℂ).arg by ring,
    Circle.exp_add, Circle.exp_arg]

lemma circleAngularArc_continuous (u v : Circle) : Continuous (circleAngularArc u v) := by
  exact (continuous_subtype_val.comp
    (Circle.exp.continuous.comp (continuous_id.mul_const _))).mul_const _

lemma circleAngularArc_zero (u v : Circle) : circleAngularArc u v 0 = u := by
  simp [circleAngularArc]

lemma circleAngularArc_one (u v : Circle) : circleAngularArc u v 1 = v := by
  change ((Circle.exp (1 * Circle.angleDiff u v) * u : Circle) : ℂ) = _
  rw [one_mul, Circle.exp_angleDiff_mul]

lemma circleAngularArc_injOn (u v : Circle) (huv : u ≠ v) :
    Set.InjOn (circleAngularArc u v) (Icc 0 1) := by
  intro s hs t ht h
  have h' : Circle.path u v ⟨s, hs⟩ = Circle.path u v ⟨t, ht⟩ := by
    apply Subtype.ext
    simpa only [← circleAngularArc_path] using h
  exact congrArg Subtype.val (Circle.path_injective_of_ne huv h')

lemma circleAngularArc_conj_mul (u v : Circle) (s t : ℝ) :
    star (circleAngularArc u v t) * circleAngularArc u v s =
      (Circle.exp ((s - t) * Circle.angleDiff u v) : ℂ) := by
  change (starRingEnd ℂ) ((Circle.exp (t * Circle.angleDiff u v) * u : Circle) : ℂ) *
    ((Circle.exp (s * Circle.angleDiff u v) * u : Circle) : ℂ) = _
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul]
  congr 1
  rw [mul_inv_rev]
  calc
    _ = (Circle.exp (t * Circle.angleDiff u v))⁻¹ *
      Circle.exp (s * Circle.angleDiff u v) * (u⁻¹ * u) := by ac_rfl
    _ = Circle.exp ((s - t) * Circle.angleDiff u v) := by
      rw [inv_mul_cancel, mul_one, ← Circle.exp_neg, ← Circle.exp_add]
      congr 1
      ring

lemma circleAngularArc_radial_determinant (u v : Circle) (s t r q : ℝ) :
    (star (q • circleAngularArc u v t - r • circleAngularArc u v t) *
      (circleAngularArc u v s - r • circleAngularArc u v t)).im =
      (q - r) * Real.sin ((s - t) * Circle.angleDiff u v) := by
  rw [← sub_smul, star_smul, smul_mul_assoc, mul_sub, mul_smul_comm,
    circleAngularArc_conj_mul, circleAngularArc_conj_mul]
  simp only [sub_self, zero_mul, Circle.exp_zero, Circle.coe_one, star_trivial,
    Complex.smul_im, smul_eq_mul, Complex.sub_im, Complex.one_im, mul_zero, sub_zero]
  rw [Circle.coe_exp, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]

lemma circleAngularArc_mem_sphere (u v : Circle) (t : ℝ) :
    circleAngularArc u v t ∈ sphere (0 : ℂ) 1 :=
  (Circle.exp (t * Circle.angleDiff u v) * u).property

/-- A nondegenerate radial segment has opposite determinant signs immediately
before and after its contact with a directed circle arc. -/
lemma circleAngularArc_radial_sign (u v : Circle) (huv : u ≠ v)
    (t : ℝ) (ht : t ∈ Ioo 0 1) (r q : ℝ) (hrq : q ≠ r) :
    ∃ δ > 0, δ < t ∧ δ < 1 - t ∧
      ∀ s ∈ Ioo (t - δ) t, ∀ w ∈ Ioo t (t + δ),
        (star (q • circleAngularArc u v t - r • circleAngularArc u v t) *
          (circleAngularArc u v s - r • circleAngularArc u v t)).im *
        (star (q • circleAngularArc u v t - r • circleAngularArc u v t) *
          (circleAngularArc u v w - r • circleAngularArc u v t)).im < 0 := by
  let d := Circle.angleDiff u v
  have hd : 0 < d := Circle.angleDiff_pos huv
  let δ := min (min t (1 - t)) (Real.pi / d) / 2
  have hm : 0 < min (min t (1 - t)) (Real.pi / d) :=
    lt_min (lt_min ht.1 (sub_pos.mpr ht.2)) (div_pos Real.pi_pos hd)
  have hδ : 0 < δ := half_pos hm
  have hδmin : δ < min (min t (1 - t)) (Real.pi / d) := half_lt_self hm
  have hδt : δ < t := hδmin.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ1 : δ < 1 - t := hδmin.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδd : δ * d < Real.pi := (lt_div_iff₀ hd).mp (hδmin.trans_le (min_le_right _ _))
  refine ⟨δ, hδ, hδt, hδ1, ?_⟩
  intro s hs w hw
  rw [circleAngularArc_radial_determinant, circleAngularArc_radial_determinant]
  have hsinS : Real.sin ((s - t) * d) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (mul_neg_of_neg_of_pos (sub_neg.mpr hs.2) hd)
      (by nlinarith [mul_lt_mul_of_pos_right hs.1 hd])
  have hsinW : 0 < Real.sin ((w - t) * d) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos (sub_pos.mpr hw.1) hd)
      (by nlinarith [mul_lt_mul_of_pos_right hw.2 hd])
  have hprod := mul_neg_of_neg_of_pos hsinS hsinW
  have hsq : 0 < (q - r) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hrq)
  have := mul_neg_of_pos_of_neg hsq hprod
  nlinarith

/-- The selected marker lies in exactly one directed open arc, and the marker
in the other punctured-circle component does not lie on its closed arc. -/
lemma circleAngularArc_select (u v : Circle) (huv : u ≠ v) (a b : ℂ)
    (ha : a ∈ sphere (0 : ℂ) 1 \ ({(u : ℂ), (v : ℂ)} : Set ℂ))
    (hb : b ∈ sphere (0 : ℂ) 1 \ ({(u : ℂ), (v : ℂ)} : Set ℂ))
    (hsep : b ∉ connectedComponentIn
      (sphere (0 : ℂ) 1 \ ({(u : ℂ), (v : ℂ)} : Set ℂ)) a) :
    ∃ x y : Circle, ({(x : ℂ), (y : ℂ)} : Set ℂ) = {(u : ℂ), (v : ℂ)} ∧
      x ≠ y ∧ ∃ t ∈ Ioo (0 : ℝ) 1, circleAngularArc x y t = a ∧
        b ∉ circleAngularArc x y '' Icc 0 1 := by
  have good (x y : Circle) (hxy : x ≠ y)
      (hends : ({(x : ℂ), (y : ℂ)} : Set ℂ) = {(u : ℂ), (v : ℂ)})
      (hta : a ∈ Set.range (fun t : unitInterval ↦ (Circle.path x y t : ℂ))) :
      ∃ t ∈ Ioo (0 : ℝ) 1, circleAngularArc x y t = a ∧
        b ∉ circleAngularArc x y '' Icc 0 1 := by
    let e : unitInterval → ℂ := fun t ↦ (Circle.path x y t : ℂ)
    have hinj : Function.Injective e :=
      Subtype.val_injective.comp (Circle.path_injective_of_ne hxy)
    have hcont : Continuous e := continuous_subtype_val.comp (Circle.path x y).continuous
    have h0 : e 0 = x := congrArg Subtype.val (Circle.path x y).source
    have h1 : e 1 = y := congrArg Subtype.val (Circle.path x y).target
    have hinter (z : ℂ) (hz : z ∉ ({(u : ℂ), (v : ℂ)} : Set ℂ))
        (t : unitInterval) (ht : e t = z) : t ∈ Ioo 0 1 := by
      constructor
      · apply unitInterval.pos_iff_ne_zero.mpr
        intro heq
        apply hz
        rw [← hends, ← ht, heq, h0]
        exact mem_insert _ _
      · apply unitInterval.lt_one_iff_ne_one.mpr
        intro heq
        apply hz
        rw [← hends, ← ht, heq, h1]
        exact mem_insert_of_mem _ (mem_singleton _)
    obtain ⟨t, ht⟩ := hta
    have htI := hinter a ha.2 t ht
    refine ⟨t, htI, (circleAngularArc_path x y t).trans ht, ?_⟩
    rintro ⟨s, hs, hsb⟩
    have hsb' : e ⟨s, hs⟩ = b := (circleAngularArc_path x y ⟨s, hs⟩).symm.trans hsb
    have hsI := hinter b hb.2 ⟨s, hs⟩ hsb'
    have hpre : IsPreconnected (e '' Ioo 0 1) := isPreconnected_Ioo.image e hcont.continuousOn
    have hsub : e '' Ioo 0 1 ⊆ sphere (0 : ℂ) 1 \ ({(u : ℂ), (v : ℂ)} : Set ℂ) := by
      rintro z ⟨w, hw, rfl⟩
      refine ⟨(Circle.path x y w).property, ?_⟩
      rw [← hends]
      rintro (hz | hz)
      · exact hw.1.ne' (hinj (hz.trans h0.symm))
      · exact hw.2.ne (hinj (hz.trans h1.symm))
    exact hsep (hpre.subset_connectedComponentIn ⟨t, htI, ht⟩ hsub ⟨⟨s, hs⟩, hsI, hsb'⟩)
  let a' : Circle := ⟨a, ha.1⟩
  have hac : a' ∈ Set.range (Circle.path u v) ∪ Set.range (Circle.path v u) := by
    rw [Circle.range_path_union_range_path huv]
    trivial
  rcases hac with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact ⟨u, v, rfl, huv, good u v huv rfl ⟨t, congrArg Subtype.val ht⟩⟩
  · refine ⟨v, u, Set.pair_comm _ _, huv.symm, good v u huv.symm (Set.pair_comm _ _) ?_⟩
    exact ⟨t, congrArg Subtype.val ht⟩

/-- An angular arc meeting a polygon only at a radial edge crosses it once,
with the precise determinant predicate used by Cairns's crossing theorem.
Source: Cairns (1951), Lemma 5.1 p.866. The whole angular arc lies on the
circle, so the prescribed two-point polygon-circle intersection and exclusion
of b leave exactly the contact a. The contact is in the open edge by assumption.
If the edge endpoints are r*a and q*a, conjugate multiplication using |a|=1
gives determinant (q-r)*sin((s-t)*angleDiff(u,v)). Nondegeneracy gives q≠r.
Choose a parameter neighborhood smaller than t, 1-t and π/angleDiff(u,v).
The two sine values have opposite strict signs, so their product times
(q-r)^2 is negative. These are precisely the single-crossing conditions. -/
theorem circleAngularArc_crossesPolygonOnce {n : ℕ} (P : Polygon ℂ n)
    (u v : Circle) (huv : u ≠ v) (a b : ℂ) (t : ℝ) (ht : t ∈ Ioo 0 1)
    (hat : circleAngularArc u v t = a)
    (hb : b ∉ circleAngularArc u v '' Icc 0 1)
    (hc : P.boundary ℝ ∩ sphere (0 : ℂ) 1 = {a, b})
    (i : Fin n) (r q : ℝ) (hr : P i = r • a) (hq : P (finRotate n i) = q • a)
    (hnd : P i ≠ P (finRotate n i))
    (hedge : a ∈ openSegment ℝ (P i) (P (finRotate n i))) :
    CrossesPolygonOnce P (circleAngularArc u v) := by
  have hrq : q ≠ r := by
    intro heq
    apply hnd
    rw [hr, hq, heq]
  refine ⟨i, t, ht, ?_, hat.symm ▸ hedge, ?_⟩
  · ext z
    constructor
    · rintro ⟨hzf, hzP⟩
      have hzS : z ∈ sphere (0 : ℂ) 1 := by
        obtain ⟨s, hs, rfl⟩ := hzf
        exact circleAngularArc_mem_sphere u v s
      have hzab : z ∈ ({a, b} : Set ℂ) := hc ▸ ⟨hzP, hzS⟩
      rcases hzab with hz | hz
      · exact Set.mem_singleton_iff.mpr (hz.trans hat.symm)
      · exact False.elim (hb (hz ▸ hzf))
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      refine ⟨⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩, ?_⟩
      rw [hat]
      exact mem_iUnion.mpr ⟨i, by
        simpa only [Polygon.edgeSet, affineSegment_eq_segment] using
          openSegment_subset_segment ℝ _ _ hedge⟩
  · rw [hr, hq, ← hat]
    exact circleAngularArc_radial_sign u v huv t ht r q hrq

end HolomorphicAnosov

