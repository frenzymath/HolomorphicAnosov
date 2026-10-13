import HolomorphicAnosov.Topology.BoundaryCycleConeG9
import HolomorphicAnosov.Topology.TrianglePresentationLengthG9
import HolomorphicAnosov.Topology.BoundaryCycleCircleG9
import HolomorphicAnosov.Topology.NormalWordHandleCircleG9
import HolomorphicAnosov.Topology.TrianglePresentationFaithfulG6
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.List.Chain
import HolomorphicAnosov.Topology.TriangleWordLengthG9
import Mathlib.Topology.Connected.TotallyDisconnected
import HolomorphicAnosov.Topology.GallierXuPresentationRelabeling
import Mathlib.Analysis.Complex.ReImTopology
import HolomorphicAnosov.Topology.GallierXuOriginalTriangleDiskChartG6
import Mathlib.Topology.Order.IntermediateValue
import HolomorphicAnosov.Topology.CircleDiskBoundaryExtension
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Homeomorph.Quotient
import HolomorphicAnosov.Topology.GallierXuSurfacePresentation

noncomputable section
open Set Topology Metric
open scoped BigOperators Classical
namespace HolomorphicAnosov.Topology.GallierXu

/-- Rotation of each parameter disk is the geometric realization of changing
its cyclic starting position. The radius is unchanged. -/
private def diskRotation (a : ℝ) : Disk ≃ₜ Disk where
  toFun z := ⟨(Circle.exp a : ℂ) * z.val, by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_mul,
      Circle.norm_coe, one_mul] using z.property⟩
  invFun z := ⟨(Circle.exp (-a) : ℂ) * z.val, by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_mul,
      Circle.norm_coe, one_mul] using z.property⟩
  left_inv z := by
    apply Subtype.ext
    change (Circle.exp (-a) : ℂ) * ((Circle.exp a : ℂ) * z.val) = z.val
    rw [← mul_assoc, ← Circle.coe_mul, ← Circle.exp_add]
    simp
  right_inv z := by
    apply Subtype.ext
    change (Circle.exp a : ℂ) * ((Circle.exp (-a) : ℂ) * z.val) = z.val
    rw [← mul_assoc, ← Circle.coe_mul, ← Circle.exp_add]
    simp
  continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_const.mul continuous_subtype_val).subtype_mk _

private theorem cyclic_angle (n r k : ℕ) (hn : 0 < n) (s : ℝ) :
    (Circle.exp (2 * Real.pi * (r : ℝ) / n) : ℂ) *
      Circle.exp (2 * Real.pi * ((k : ℝ) + s) / n) =
    Circle.exp (2 * Real.pi * (((k + r) % n : ℕ) + s) / n) := by
  rw [← Circle.coe_mul, ← Circle.exp_add]
  apply congrArg Subtype.val
  apply Circle.exp_eq_exp.mpr
  refine ⟨((k + r) / n : ℕ), ?_⟩
  have hdiv : (((k + r) % n : ℕ) : ℝ) +
      (n : ℝ) * (((k + r) / n : ℕ) : ℝ) = (k : ℝ) + r := by
    exact_mod_cast Nat.mod_add_div (k + r) n
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [Int.cast_natCast]
  field_simp [hn']
  nlinarith [congrArg (fun x : ℝ ↦ 2 * Real.pi * x) hdiv]

private theorem rotate_faces_realized {P Q : Presentation}
    (f : Fin Q.length ≃ Fin P.length) (r : Fin Q.length → ℕ)
    (h : ∀ k, (P.get (f k)).rotate (r k) = Q.get k) :
    ∃ H : Realization Q ≃ₜ Realization P,
      RespectsParameters (.reindex ⟨f, fun k ↦ List.IsRotated.symm ⟨r k, h k⟩⟩) H := by
  classical
  have hlen (k : Fin Q.length) : (Q.get k).length = (P.get (f k)).length := by
    rw [← h k, List.length_rotate]
  let shift (k : Fin Q.length) : Equiv.Perm (Fin (P.get (f k)).length) :=
    if hn : 0 < (P.get (f k)).length then
      finCycle ⟨r k % (P.get (f k)).length, Nat.mod_lt _ hn⟩ else Equiv.refl _
  let pos (k : Fin Q.length) : Fin (Q.get k).length ≃ Fin (P.get (f k)).length :=
    (finCongr (hlen k)).trans (shift k)
  have hval (k : Fin Q.length) (j : Fin (Q.get k).length) :
      (pos k j).val = (j.val + r k) % (P.get (f k)).length := by
    have hn : 0 < (P.get (f k)).length := (hlen k) ▸ j.pos
    dsimp only [pos, Equiv.trans_apply, shift]
    rw [dite_eq_left hn]
    simp only [finCycle_apply, Fin.add_def, finCongr_apply, Fin.val_cast, Nat.add_mod,
      Nat.mod_mod]
  have hget (k : Fin Q.length) (j : Fin (Q.get k).length) :
      (Q.get k).get j = (P.get (f k)).get (pos k j) := by
    have hj : j.val < (P.get (f k)).length := (hlen k) ▸ j.isLt
    have hh := congrArg (fun w : Word ↦ w[j.val]?) (h k)
    rw [List.getElem?_rotate hj] at hh
    simp only [List.getElem?_eq_getElem j.isLt,
      List.getElem?_eq_getElem (Nat.mod_lt _ (Nat.zero_lt_of_lt hj))] at hh
    simpa only [List.get_eq_getElem, hval] using (Option.some.inj hh).symm
  let angle (k : Fin Q.length) : ℝ :=
    2 * Real.pi * (r k : ℝ) / (P.get (f k)).length
  have hside (k : Fin Q.length) (j : Fin (Q.get k).length) (t : ℝ) :
      (Circle.exp (angle k) : ℂ) * sidePoint Q k j t =
        sidePoint P (f k) (pos k j) t := by
    simp only [sidePoint, hget, hlen, hval, angle]
    exact cyclic_angle _ _ _ ((hlen k) ▸ j.pos) _
  let F : FaceDisks Q ≃ₜ FaceDisks P := {
    toFun := fun x ↦ (f x.1, diskRotation (angle x.1) x.2)
    invFun := fun y ↦ (f.symm y.1, (diskRotation (angle (f.symm y.1))).symm y.2)
    left_inv := by intro x; simp
    right_inv := by intro y; simp
    continuous_toFun := by
      change Continuous (fun x : Fin Q.length × Disk ↦
        (f x.1, diskRotation (angle x.1) x.2))
      apply continuous_prod_of_discrete_left.mpr
      intro k
      exact (continuous_const : Continuous (fun _ : Disk ↦ f k)).prodMk
        (diskRotation (angle k)).continuous
    continuous_invFun := by
      change Continuous (fun y : Fin P.length × Disk ↦
        (f.symm y.1, (diskRotation (angle (f.symm y.1))).symm y.2))
      apply continuous_prod_of_discrete_left.mpr
      intro k
      exact (continuous_const : Continuous (fun _ : Disk ↦ f.symm k)).prodMk
        (diskRotation (angle (f.symm k))).symm.continuous }
  have hedge (x y : FaceDisks Q) :
      edgeIdentification Q x y ↔ edgeIdentification P (F x) (F y) := by
    constructor
    · rintro ⟨j, k, t, ht, he, hx, hy⟩
      refine ⟨pos x.1 j, pos y.1 k, t, ht, ?_, ?_, ?_⟩
      · exact (hget x.1 j).symm ▸ ((hget y.1 k).symm ▸ he)
      · change (Circle.exp (angle x.1) : ℂ) * x.2.val = _
        rw [hx, hside]
        rfl
      · change (Circle.exp (angle y.1) : ℂ) * y.2.val = _
        rw [hy, hside]
        rfl
    · intro hxy
      change edgeIdentification P (f x.1, diskRotation (angle x.1) x.2)
        (f y.1, diskRotation (angle y.1) y.2) at hxy
      obtain ⟨j, k, t, ht, he, hx, hy⟩ := hxy
      obtain ⟨j, rfl⟩ := (pos x.1).surjective j
      obtain ⟨k, rfl⟩ := (pos y.1).surjective k
      refine ⟨j, k, t, ht, ?_, ?_, ?_⟩
      · rw [hget, hget]
        exact he
      · apply mul_left_cancel₀ (Circle.coe_ne_zero _) 
        change (Circle.exp (angle x.1) : ℂ) * x.2.val = _
        rw [hside]
        exact hx
      · apply mul_left_cancel₀ (Circle.coe_ne_zero _)
        change (Circle.exp (angle y.1) : ℂ) * y.2.val = _
        rw [hside]
        exact hy
  have hrel (x y : FaceDisks Q) :
      Relation.EqvGen (edgeIdentification Q) x y ↔
        Relation.EqvGen (edgeIdentification P) (F x) (F y) := by
    constructor
    · intro hxy
      induction hxy with
      | rel a b hab => exact .rel _ _ ((hedge a b).mp hab)
      | refl a => exact .refl _
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'
    · intro hxy
      have hh : ∀ a b, Relation.EqvGen (edgeIdentification P) a b →
          Relation.EqvGen (edgeIdentification Q) (F.symm a) (F.symm b) := by
        intro a b hab
        induction hab with
        | rel a b hab =>
          apply Relation.EqvGen.rel
          apply (hedge _ _).mpr
          simpa only [F.apply_symm_apply] using hab
        | refl a => exact .refl _
        | symm _ _ _ ih => exact ih.symm
        | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'
      simpa only [F.symm_apply_apply] using hh _ _ hxy
  let H : Realization Q ≃ₜ Realization P := Homeomorph.Quotient.congr F hrel
  refine ⟨H, ?_⟩
  intro x y j k t s ht hs hparam hx hy
  change ((Q.get x.1).get j).1 = ((P.get y.1).get k).1 ∧ t = s at hparam
  change project P (F x) = project P y
  apply Quotient.sound
  apply Relation.EqvGen.rel
  refine ⟨pos x.1 j, k, s, hs, ?_, ?_, hy⟩
  · change ((P.get (f x.1)).get (pos x.1 j)).1 = _
    rw [← hget]
    exact hparam.1
  · change (Circle.exp (angle x.1) : ℂ) * x.2.val = _
    rw [hx, hside, hparam.2]
    rfl

/-- Cyclic starts and face enumeration changes preserve the realized quotient
and every surviving edge parameter. Source: Gallier–Xu Definitions 6.1–6.3,
pp.79–86. Rotate each round parameter disk by the angle associated with its
cyclic index offset. The side-point identity differs by an integral full turn,
so equal-label interval identifications are preserved and reflected. The disk
homeomorphism descends to inverse quotient maps with the same parameters. -/
theorem reindex_realized {P Q : Presentation} (h : Reindexed P Q) :
    ∃ H : Realization P ≃ₜ Realization Q, RespectsParameters (.reindex h) H := by
  obtain ⟨f, hf⟩ := h
  have hh (k : Fin P.length) : ∃ r : ℕ, (Q.get (f k)).rotate r = P.get k :=
    (hf k).symm
  choose r hr using hh
  obtain ⟨H, hH⟩ := rotate_faces_realized f r hr
  exact ⟨H, hH⟩

/-- Reversing a realized elementary step reverses its exact edge parameters. -/
theorem RespectsParameters.symm {P Q : Presentation} {h : Elementary P Q}
    {H : Realization P ≃ₜ Realization Q} (hH : RespectsParameters h H) :
    RespectsParameters h.inverse H.symm := by
  intro x y i j t s ht hs hp hx hy
  apply H.injective
  rw [H.apply_symm_apply]
  exact (hH y x j i s t hs ht hp hy hx).symm

/-- A realized sequence can be traversed in the reverse direction. -/
def RealizedSequence.reverse {P Q : Presentation} (s : RealizedSequence P Q) :
    RealizedSequence Q P :=
  match s with
  | .nil P => .nil P
  | .cons h H hH tail => tail.reverse.trans (.cons h.inverse H.symm hH.symm (.nil _))

@[simp] theorem RealizedSequence.reverse_homeomorph_apply {P Q : Presentation}
    (s : RealizedSequence P Q) (x : Realization Q) :
    s.reverse.homeomorph x = s.homeomorph.symm x := by
  induction s with
  | nil P => rfl
  | cons h H hH tail ih =>
    simp only [RealizedSequence.reverse, RealizedSequence.trans_homeomorph_apply,
      RealizedSequence.homeomorph, Homeomorph.trans_apply, Homeomorph.refl_apply,
      Homeomorph.symm_trans_apply, ih, id_eq]

/-- The normal word has four sides per handle and three per boundary component. -/
theorem normalWord_length (g b : ℕ) : (normalWord g b).length = 4 * g + 3 * b := by
  simp [normalWord, List.length_flatMap, mul_comm]

/-- Every normal-form edge label occurs below the exact handle/boundary bound. -/
theorem normalWord_label_bound {g b a : ℕ} {s : Bool}
    (h : (a, s) ∈ normalWord g b) : a < 2 * g + 2 * b := by
  simp only [normalWord, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨i, hi, he | he | he | he⟩ | ⟨j, hj, he | he | he⟩ <;>
    rcases he with ⟨rfl, _⟩ <;> omega

/-- The labels of the normal word are exactly its consecutive handle, spoke,
and boundary labels; no unused labels are counted. -/
theorem normalWord_labels (g b : ℕ) : labels [normalWord g b] = Finset.range (2 * g + 2 * b) := by
  ext a
  simp only [labels, occurrences, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.mem_toFinset, List.mem_map, Finset.mem_range]
  constructor
  · rintro ⟨⟨k, s⟩, h, rfl⟩
    exact normalWord_label_bound h
  · intro ha
    by_cases hg : a < 2 * g
    · have hi : a / 2 < g := by omega
      have he : a = 2 * (a / 2) ∨ a = 2 * (a / 2) + 1 := by omega
      refine ⟨(a, true), ?_, rfl⟩
      apply List.mem_append_left
      apply List.mem_flatMap.mpr
      refine ⟨a / 2, List.mem_range.mpr hi, ?_⟩
      simpa only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
        Bool.true_eq_false, and_false, or_false, and_true] using he
    · have hj : (a - 2 * g) / 2 < b := by omega
      have he : a = 2 * g + 2 * ((a - 2 * g) / 2) ∨
          a = 2 * g + 2 * ((a - 2 * g) / 2) + 1 := by omega
      refine ⟨(a, true), ?_, rfl⟩
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨(a - 2 * g) / 2, List.mem_range.mpr hj, ?_⟩
      simpa only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
        Bool.true_eq_false, and_false, or_false, and_true] using he

@[simp] theorem normalWord_labels_card (g b : ℕ) :
    (labels [normalWord g b]).card = 2 * g + 2 * b := by
  rw [normalWord_labels, Finset.card_range]

/-- An increasing reparameterization of the closed angular interval descends
to the parameter circle and extends radially over the disk. -/
private theorem interval_reparameterization_disk
    (h : Icc (0 : ℝ) (0 + 1) ≃o Icc (0 : ℝ) (0 + 1)) :
    ∃ H : Disk ≃ₜ Disk, ∀ t : Icc (0 : ℝ) (0 + 1),
      (H ⟨Circle.exp (2 * Real.pi * t.val), by
        rw [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe]⟩ : ℂ) =
        Circle.exp (2 * Real.pi * (h t).val) := by
  let : Fact ((0 : ℝ) ≤ 0 + 1) := ⟨by norm_num⟩
  let e : Icc (0 : ℝ) (0 + 1) ≃ₜ Icc (0 : ℝ) (0 + 1) := h.toHomeomorph
  have he : ∀ x y, AddCircle.EndpointIdent (1 : ℝ) 0 x y ↔
      AddCircle.EndpointIdent (1 : ℝ) 0 (e x) (e y) := by
    intro x y
    constructor
    · intro hxy
      cases hxy
      have hb : e (⟨0, by norm_num⟩ : Icc (0 : ℝ) (0 + 1)) = ⟨0, by norm_num⟩ :=
        h.map_bot
      have ht : e (⟨0 + 1, by norm_num⟩ : Icc (0 : ℝ) (0 + 1)) = ⟨0 + 1, by norm_num⟩ :=
        h.map_top
      rw [hb, ht]
      exact .mk
    · intro hxy
      have hh : ∀ a b, AddCircle.EndpointIdent (1 : ℝ) 0 a b →
          AddCircle.EndpointIdent (1 : ℝ) 0 (e.symm a) (e.symm b) := by
        intro a b hab
        cases hab
        have hb : e.symm (⟨0, by norm_num⟩ : Icc (0 : ℝ) (0 + 1)) = ⟨0, by norm_num⟩ :=
          h.symm.map_bot
        have ht : e.symm (⟨0 + 1, by norm_num⟩ : Icc (0 : ℝ) (0 + 1)) = ⟨0 + 1, by norm_num⟩ :=
          h.symm.map_top
        rw [hb, ht]
        exact .mk
      simpa only [e.symm_apply_apply] using hh _ _ hxy
  let q := AddCircle.homeoIccQuot (1 : ℝ) 0
  let c := AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)
  let b : Circle ≃ₜ Circle := c.symm.trans
    (q.trans ((Homeomorph.Quot.congr e he).trans (q.symm.trans c)))
  obtain ⟨H, hH⟩ := HolomorphicAnosov.circle_disk_boundary_extension b
  refine ⟨H, ?_⟩
  intro t
  rw [hH]
  have hc (s : Icc (0 : ℝ) (0 + 1)) :
      c (q.symm (Quot.mk _ s)) = Circle.exp (2 * Real.pi * s.val) := by
    change AddCircle.homeomorphCircle _ (s.val : AddCircle (1 : ℝ)) = _
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
    simp
  rw [← hc t]
  change (c (q.symm ((Homeomorph.Quot.congr e he)
    (q (c.symm (c (q.symm (Quot.mk _ t))))))) : ℂ) = _
  rw [c.symm_apply_apply, q.apply_symm_apply]
  exact congrArg Subtype.val (hc (h t))

private def angularBend (a b x : ℝ) : ℝ :=
  if x ≤ a then b * (x / a) else b + (1 - b) * ((x - a) / (1 - a))

private theorem angularBend_mem {a b x : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    angularBend a b x ∈ Icc (0 : ℝ) 1 := by
  have ha' : 0 < 1 - a := sub_pos.mpr ha.2
  have hb' : 0 < 1 - b := sub_pos.mpr hb.2
  unfold angularBend
  split_ifs with h
  · have hratio : 0 ≤ x / a ∧ x / a ≤ 1 :=
      ⟨div_nonneg hx.1 ha.1.le, (div_le_one ha.1).mpr h⟩
    constructor
    · exact mul_nonneg hb.1.le hratio.1
    · nlinarith [mul_nonneg hb.1.le hratio.1, mul_le_mul_of_nonneg_left hratio.2 hb.1.le]
  · have hratio : 0 ≤ (x - a) / (1 - a) ∧ (x - a) / (1 - a) ≤ 1 :=
      ⟨div_nonneg (by linarith) ha'.le, (div_le_one ha').mpr (by linarith [hx.2])⟩
    constructor
    · exact add_nonneg hb.1.le (mul_nonneg hb'.le hratio.1)
    · nlinarith [mul_le_mul_of_nonneg_left hratio.2 hb'.le]

private theorem angularBend_left_inverse {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hb : b ∈ Ioo (0 : ℝ) 1) (x : ℝ) :
    angularBend b a (angularBend a b x) = x := by
  have ha' : 0 < 1 - a := sub_pos.mpr ha.2
  have hb' : 0 < 1 - b := sub_pos.mpr hb.2
  by_cases hx : x ≤ a
  · have he : angularBend a b x = b * (x / a) := ite_eq_left hx
    have hh : angularBend a b x ≤ b := by
      rw [he]
      calc b * (x / a) ≤ b * 1 := mul_le_mul_of_nonneg_left ((div_le_one ha.1).mpr hx) hb.1.le
           _ = b := mul_one b
    rw [angularBend, ite_eq_left hh, he]
    field_simp [ne_of_gt ha.1, ne_of_gt hb.1]
  · have he : angularBend a b x = b + (1 - b) * ((x - a) / (1 - a)) := ite_eq_right hx
    have hh : ¬ angularBend a b x ≤ b := by
      rw [he]
      have : 0 < (1 - b) * ((x - a) / (1 - a)) :=
        mul_pos hb' (div_pos (by linarith) ha')
      linarith
    rw [angularBend, ite_eq_right hh, he]
    field_simp [ne_of_gt ha', ne_of_gt hb']
    ; ring

private theorem angularBend_strictMono {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hb : b ∈ Ioo (0 : ℝ) 1) : StrictMono (angularBend a b) := by
  intro x y hxy
  have ha' : 0 < 1 - a := sub_pos.mpr ha.2
  have hb' : 0 < 1 - b := sub_pos.mpr hb.2
  unfold angularBend
  split_ifs with hx hy hy
  · exact mul_lt_mul_of_pos_left ((div_lt_div_iff_of_pos_right ha.1).mpr hxy) hb.1
  · have hlo : b * (x / a) ≤ b := by
      calc b * (x / a) ≤ b * 1 := mul_le_mul_of_nonneg_left ((div_le_one ha.1).mpr hx) hb.1.le
           _ = b := mul_one b
    have hhi : 0 < (1 - b) * ((y - a) / (1 - a)) :=
      mul_pos hb' (div_pos (by linarith) ha')
    linarith
  · exact False.elim (hx (hxy.le.trans hy))
  · simpa only [add_comm] using add_lt_add_left (mul_lt_mul_of_pos_left
      ((div_lt_div_iff_of_pos_right ha').mpr (sub_lt_sub_right hxy a)) hb') b

private def angularBendOrderIso {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hb : b ∈ Ioo (0 : ℝ) 1) :
    Icc (0 : ℝ) (0 + 1) ≃o Icc (0 : ℝ) (0 + 1) where
  toFun x := ⟨angularBend a b x.val, by simpa using angularBend_mem ha hb (by simpa using x.property)⟩
  invFun y := ⟨angularBend b a y.val, by simpa using angularBend_mem hb ha (by simpa using y.property)⟩
  left_inv x := Subtype.ext (angularBend_left_inverse ha hb x.val)
  right_inv y := Subtype.ext (angularBend_left_inverse hb ha y.val)
  map_rel_iff' := (angularBend_strictMono ha hb).le_iff_le

private def subdivisionAngle (n : ℕ) (S : Finset ℕ) (x : ℝ) : ℝ :=
  ((n : ℝ) * x + ∑ j ∈ S, max 0 (min 1 ((n : ℝ) * x - j))) / (n + S.card)

private theorem subdivisionAngle_strictMono {n : ℕ} (hn : 0 < n) (S : Finset ℕ) :
    StrictMono (subdivisionAngle n S) := by
  intro x y hxy
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : (0 : ℝ) < n + S.card := by positivity
  apply (div_lt_div_iff_of_pos_right hd).mpr
  apply add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hxy hn')
  apply Finset.sum_le_sum
  intro j hj
  gcongr

private theorem subdivisionAngle_continuous (n : ℕ) (S : Finset ℕ) :
    Continuous (subdivisionAngle n S) := by
  unfold subdivisionAngle
  fun_prop

private theorem subdivisionAngle_zero (n : ℕ) (S : Finset ℕ) :
    subdivisionAngle n S 0 = 0 := by
  simp [subdivisionAngle]

private theorem subdivisionAngle_one {n : ℕ} (hn : 0 < n)
    (S : Finset ℕ) (hS : ∀ j ∈ S, j < n) : subdivisionAngle n S 1 = 1 := by
  have ht (j : ℕ) (hj : j ∈ S) : max (0 : ℝ) (min 1 ((n : ℝ) * 1 - j)) = 1 := by
    have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hS j hj
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  have hsum : (∑ j ∈ S, max (0 : ℝ) (min 1 ((n : ℝ) * 1 - j))) = S.card := by
    calc
      _ = ∑ _j ∈ S, (1 : ℝ) := Finset.sum_congr rfl ht
      _ = S.card := by simp
  unfold subdivisionAngle
  rw [hsum, mul_one]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_self (by positivity)

private theorem subdivision_disk_reparameterization {n : ℕ} (hn : 0 < n)
    (S : Finset ℕ) (hS : ∀ j ∈ S, j < n) :
    ∃ H : Disk ≃ₜ Disk, ∀ t : Icc (0 : ℝ) 1,
      (H ⟨Circle.exp (2 * Real.pi * t.val), by
        rw [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe]⟩ : ℂ) =
      Circle.exp (2 * Real.pi * subdivisionAngle n S t.val) := by
  have hc := subdivisionAngle_continuous n S
  have hm := subdivisionAngle_strictMono hn S
  have himg : subdivisionAngle n S '' Icc (0 : ℝ) (0 + 1) = Icc (0 : ℝ) (0 + 1) := by
    rw [hc.continuousOn.image_Icc_of_monotoneOn (by norm_num) (hm.monotone.monotoneOn _)]
    simp only [zero_add, subdivisionAngle_zero, subdivisionAngle_one hn S hS]
  let e : Icc (0 : ℝ) (0 + 1) ≃o Icc (0 : ℝ) (0 + 1) :=
    (StrictMonoOn.orderIso (subdivisionAngle n S) _ (hm.strictMonoOn _)).trans
      (Set.orderIsoOfEq _ _ himg)
  obtain ⟨H, hH⟩ := interval_reparameterization_disk e
  refine ⟨H, ?_⟩
  intro t
  exact hH ⟨t.val, by simp⟩

private theorem subdivisionAngle_side {n : ℕ} (hn : 0 < n) (S : Finset ℕ)
    (j : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    subdivisionAngle n S (((j : ℝ) + t) / n) =
      ((j : ℝ) + (S.filter (fun k ↦ k < j)).card + t + if j ∈ S then t else 0) /
        (n + S.card) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hmul : (n : ℝ) * (((j : ℝ) + t) / n) = j + t := by field_simp
  have hterm (k : ℕ) : max (0 : ℝ) (min 1 ((j : ℝ) + t - k)) =
      (if k < j then 1 else 0) + if k = j then t else 0 := by
    by_cases hk : k < j
    · have hh : (k : ℝ) + 1 ≤ j := by exact_mod_cast hk
      rw [ite_eq_left hk, ite_eq_right (by omega), add_zero, min_eq_left (by linarith [ht.1]),
        max_eq_right zero_le_one]
    · by_cases hkj : k = j
      · subst k
        simp [min_eq_right ht.2, max_eq_right ht.1]
      · have hh : (j : ℝ) + 1 ≤ k := by exact_mod_cast (show j < k by omega)
        rw [ite_eq_right hk, ite_eq_right hkj, add_zero,
          min_eq_right (by linarith [ht.2]), max_eq_left (by linarith [ht.2])]
  unfold subdivisionAngle
  rw [hmul]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have hleft : (∑ k ∈ S, if k < j then (1 : ℝ) else 0) =
      (S.filter (fun k ↦ k < j)).card := by
    rw [← Finset.sum_filter]
    simp
  have hright : (∑ k ∈ S, if k = j then t else 0) = if j ∈ S then t else 0 := by
    simp
  rw [hleft, hright]
  congr 1
  ring

private def splitDart (a b c : ℕ) (d : Dart) : Word :=
  if d.1 = a then
    if d.2 then [(b, true), (c, true)] else [(c, false), (b, false)]
  else [d]

private theorem splitDart_length (a b c : ℕ) (d : Dart) :
    (splitDart a b c d).length = 1 + if d.1 = a then 1 else 0 := by
  unfold splitDart
  split <;> simp_all
  split <;> rfl

private theorem splitWord_length (w : Word) (a b c : ℕ) :
    (w.flatMap (splitDart a b c)).length =
      w.length + w.countP (fun d ↦ d.1 == a) := by
  induction w with
  | nil => simp
  | cons d w ih =>
    simp only [List.flatMap_cons, List.length_append, splitDart_length, ih,
      List.length_cons, List.countP_cons, beq_iff_eq]
    split <;> omega

private def splitPositions (w : Word) (a : ℕ) : Finset ℕ :=
  (Finset.range w.length).filter fun k ↦ (w[k]!).1 = a

private theorem splitPositions_prefix (w : Word) (a : ℕ) {j : ℕ} (hj : j ≤ w.length) :
    ((Finset.range j).filter fun k ↦ (w[k]!).1 = a).card =
      (w.take j).countP (fun d ↦ d.1 == a) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : j < w.length := by omega
    rw [Finset.range_add_one, Finset.filter_insert,
      List.take_succ_eq_append_getElem hj', List.countP_append, ← ih (by omega)]
    simp only [List.countP_cons, List.countP_nil, beq_iff_eq, getElem!_pos w j hj']
    split <;> simp_all

private theorem splitPositions_card (w : Word) (a : ℕ) :
    (splitPositions w a).card = w.countP (fun d ↦ d.1 == a) := by
  simpa [splitPositions] using splitPositions_prefix w a (le_refl w.length)

private theorem splitPositions_before (w : Word) (a : ℕ) {j : ℕ} (hj : j ≤ w.length) :
    ((splitPositions w a).filter fun k ↦ k < j).card =
      (w.take j).countP (fun d ↦ d.1 == a) := by
  have heq : (splitPositions w a).filter (fun k ↦ k < j) =
      (Finset.range j).filter (fun k ↦ (w[k]!).1 = a) := by
    ext k
    simp only [splitPositions, Finset.mem_filter, Finset.mem_range]
    omega
  rw [heq]
  exact splitPositions_prefix w a hj

private theorem flatMap_get_at {α β : Type*} (w : List α) (f : α → List β)
    (j : Fin w.length) (k : Fin (f (w.get j)).length) :
    ∃ h : ((w.take j.val).flatMap f).length + k.val < (w.flatMap f).length,
      (w.flatMap f)[((w.take j.val).flatMap f).length + k.val]'h = (f (w.get j)).get k := by
  have hw : w = w.take j.val ++ w.get j :: w.drop (j.val + 1) := by
    simpa only [List.get_eq_getElem, List.take_succ_eq_append_getElem j.isLt,
      List.append_assoc, List.singleton_append] using (List.take_append_drop (j.val + 1) w).symm
  have hflat : w.flatMap f = (w.take j.val).flatMap f ++
      (f (w.get j) ++ (w.drop (j.val + 1)).flatMap f) := by
    conv_lhs => rw [hw]
    simp only [List.flatMap_append, List.flatMap_cons]
  rw [hflat]
  simp only [List.length_append]
  refine ⟨by omega, ?_⟩
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem_append_left k.isLt]
  rfl

private theorem flatMap_index {α β : Type*} (w : List α) (f : α → List β)
    (l : Fin (w.flatMap f).length) :
    ∃ j : Fin w.length, ∃ k : Fin (f (w.get j)).length,
      l.val = ((w.take j.val).flatMap f).length + k.val := by
  induction w with
  | nil => exact Fin.elim0 l
  | cons d w ih =>
    by_cases hl : l.val < (f d).length
    · exact ⟨⟨0, by simp⟩, ⟨l.val, hl⟩, by simp⟩
    · have hl' : l.val - (f d).length < (w.flatMap f).length := by
        have := l.isLt
        simp only [List.flatMap_cons, List.length_append] at this
        omega
      obtain ⟨j, k, hjk⟩ := ih ⟨l.val - (f d).length, hl'⟩
      refine ⟨j.succ, k, ?_⟩
      simp only [Fin.val_succ, List.take_succ_cons, List.flatMap_cons, List.length_append]
      simp only [] at hjk
      omega

private theorem splitWord_disk (w : Word) (hw : 0 < w.length) (a b c : ℕ) :
    ∃ H : Disk ≃ₜ Disk, ∀ (j : Fin w.length) (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1),
      (H ⟨(Circle.exp (2 * Real.pi * (((j.val : ℝ) + t) / w.length)) : ℂ), by
          rw [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe]⟩ : ℂ) =
      Circle.exp (2 * Real.pi *
        ((((w.take j.val).flatMap (splitDart a b c)).length : ℝ) +
          if (w.get j).1 = a then 2 * t else t) / (w.flatMap (splitDart a b c)).length) := by
  obtain ⟨H, hH⟩ := subdivision_disk_reparameterization hw (splitPositions w a)
    (by intro k hk; exact Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
  refine ⟨H, ?_⟩
  intro j t ht
  have hn : (0 : ℝ) < w.length := by exact_mod_cast hw
  have hj : (j.val : ℝ) + 1 ≤ w.length := by exact_mod_cast j.isLt
  have hx : ((j.val : ℝ) + t) / w.length ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (add_nonneg (Nat.cast_nonneg _) ht.1) hn.le
    · rw [div_le_one hn]
      linarith [ht.2]
  rw [hH ⟨_, hx⟩]
  congr 2
  rw [subdivisionAngle_side hw _ _ ht, splitPositions_before w a (Nat.le_of_lt j.isLt),
    splitPositions_card, splitWord_length, splitWord_length]
  simp only [List.length_take, min_eq_left (Nat.le_of_lt j.isLt), Nat.cast_add]
  have hmem : j.val ∈ splitPositions w a ↔ (w.get j).1 = a := by
    simp [splitPositions, j.isLt, List.get_eq_getElem]
  rw [if_congr hmem rfl rfl]
  split <;> ring

private def splitParameter (a b c e : ℕ) (t : ℝ) (f : ℕ) (s : ℝ) : Prop :=
  (e ≠ a ∧ f = e ∧ s = t) ∨
  (e = a ∧ f = b ∧ t ≤ 1 / 2 ∧ s = 2 * t) ∨
  (e = a ∧ f = c ∧ 1 / 2 ≤ t ∧ s = 2 * t - 1)

private def dartParameter (d : Dart) (t : ℝ) : ℝ := if d.2 then t else 1 - t

private def splitTarget (a b c e : ℕ) (t : ℝ) : ℕ × ℝ :=
  if e = a then if t ≤ 1 / 2 then (b, 2 * t) else (c, 2 * t - 1) else (e, t)

private theorem splitDart_forward (a b c : ℕ) (d : Dart) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ k : Fin (splitDart a b c d).length, ∃ s ∈ Icc (0 : ℝ) 1,
      (((splitDart a b c d).get k).1, s) = splitTarget a b c d.1 t ∧
      (if d.1 = a then 2 * dartParameter d t else dartParameter d t) =
        k.val + dartParameter ((splitDart a b c d).get k) s := by
  rcases d with ⟨e, v⟩
  by_cases he : e = a
  · subst e
    cases v <;> by_cases hhalf : t ≤ 1 / 2
    all_goals simp only [one_div] at hhalf
    · refine ⟨⟨1, by simp [splitDart]⟩, 2 * t, ⟨by linarith [ht.1], by linarith⟩, ?_, ?_⟩
      · simp [splitTarget, splitDart, hhalf]
      · simp [splitDart, dartParameter]; ring
    · refine ⟨⟨0, by simp [splitDart]⟩, 2 * t - 1,
        ⟨by linarith, by linarith [ht.2]⟩, ?_, ?_⟩
      · simp [splitTarget, splitDart, hhalf]
      · simp [splitDart, dartParameter]; ring
    · refine ⟨⟨0, by simp [splitDart]⟩, 2 * t, ⟨by linarith [ht.1], by linarith⟩, ?_, ?_⟩
      · simp [splitTarget, splitDart, hhalf]
      · simp [splitDart, dartParameter]
    · refine ⟨⟨1, by simp [splitDart]⟩, 2 * t - 1,
        ⟨by linarith, by linarith [ht.2]⟩, ?_, ?_⟩
      · simp [splitTarget, splitDart, hhalf]
      · simp [splitDart, dartParameter]
  · refine ⟨⟨0, by simp [splitDart, he]⟩, t, ht, ?_, ?_⟩
    · simp [splitTarget, splitDart, he]
    · simp [splitDart, he]

private theorem splitDart_backward (a b c : ℕ) (d : Dart)
    (k : Fin (splitDart a b c d).length) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ t ∈ Icc (0 : ℝ) 1,
      splitParameter a b c d.1 t ((splitDart a b c d).get k).1 s ∧
      (if d.1 = a then 2 * dartParameter d t else dartParameter d t) =
        k.val + dartParameter ((splitDart a b c d).get k) s := by
  rcases d with ⟨e, v⟩
  by_cases he : e = a
  · subst e
    cases v <;> have hk : k.val = 0 ∨ k.val = 1 := by
      have := k.isLt
      simp only [splitDart, Bool.false_eq_true, ↓reduceIte, List.length_cons,
        List.length_nil] at this
      omega
    all_goals rcases hk with hk | hk
    all_goals rcases k with ⟨k, hklt⟩; simp only [] at hk; subst k
    · refine ⟨(s + 1) / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_, ?_⟩
      · simp [splitParameter, splitDart, List.get_eq_getElem]
        right
        exact ⟨by linarith [hs.1], by ring⟩
      · simp [splitDart, dartParameter, List.get_eq_getElem]; ring
    · refine ⟨s / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_, ?_⟩
      · simp [splitParameter, splitDart, List.get_eq_getElem]
        left
        exact ⟨by linarith [hs.2], by ring⟩
      · simp [splitDart, dartParameter, List.get_eq_getElem]; ring
    · refine ⟨s / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_, ?_⟩
      · simp [splitParameter, splitDart, List.get_eq_getElem]
        left
        exact ⟨by linarith [hs.2], by ring⟩
      · simp [splitDart, dartParameter, List.get_eq_getElem]; ring
    · refine ⟨(s + 1) / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_, ?_⟩
      · simp [splitParameter, splitDart, List.get_eq_getElem]
        right
        exact ⟨by linarith [hs.1], by ring⟩
      · simp [splitDart, dartParameter, List.get_eq_getElem]; ring
  · have hk : k.val = 0 := by
      have := k.isLt
      simp [splitDart, he] at this
      omega
    rcases k with ⟨k, hklt⟩
    simp only [] at hk
    subst k
    refine ⟨s, hs, ?_, ?_⟩
    · simp [splitParameter, splitDart, he, List.get_eq_getElem]
    · simp [splitDart, he, List.get_eq_getElem]

private theorem splitParameter_injective {a b c e e' f : ℕ} {t t' s : ℝ}
    (hb : e ≠ b) (hc : e ≠ c) (hb' : e' ≠ b) (hc' : e' ≠ c) (hbc : b ≠ c)
    (h : splitParameter a b c e t f s) (h' : splitParameter a b c e' t' f s) :
    e = e' ∧ t = t' := by
  rcases h with ⟨h, hf, hs⟩ | ⟨rfl, rfl, _, hs⟩ | ⟨rfl, rfl, _, hs⟩ <;>
    rcases h' with ⟨h', hf', hs'⟩ | ⟨he', hf', _, hs'⟩ | ⟨he', hf', _, hs'⟩
  all_goals first | exact ⟨by omega, by linarith⟩ | omega

private def wordPoint (w : Word) (j : Fin w.length) (t : ℝ) : Disk :=
  ⟨(Circle.exp (2 * Real.pi * (j.val + dartParameter (w.get j) t) / w.length) : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe]⟩

private def splitWordChart (w : Word) (a b c : ℕ) : Disk ≃ₜ Disk :=
  if h : 0 < w.length then (splitWord_disk w h a b c).choose else Homeomorph.refl _

private theorem splitWordChart_spec (w : Word) (a b c : ℕ) (j : Fin w.length)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (splitWordChart w a b c (wordPoint w j t) : ℂ) =
      Circle.exp (2 * Real.pi *
        ((((w.take j.val).flatMap (splitDart a b c)).length : ℝ) +
          if (w.get j).1 = a then 2 * dartParameter (w.get j) t
            else dartParameter (w.get j) t) / (w.flatMap (splitDart a b c)).length) := by
  have hw : 0 < w.length := j.pos
  have ht' : dartParameter (w.get j) t ∈ Icc (0 : ℝ) 1 := by
    unfold dartParameter
    split
    · exact ht
    · exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h := (splitWord_disk w hw a b c).choose_spec j (dartParameter (w.get j) t) ht'
  simpa only [splitWordChart, dite_eq_left hw, wordPoint, mul_div_assoc] using h

private theorem splitWordChart_side (w : Word) (a b c : ℕ) (j : Fin w.length)
    (k : Fin (splitDart a b c (w.get j)).length) {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1)
    (ha : (if (w.get j).1 = a then 2 * dartParameter (w.get j) t
        else dartParameter (w.get j) t) =
      k.val + dartParameter ((splitDart a b c (w.get j)).get k) s) :
    ∃ l : Fin (w.flatMap (splitDart a b c)).length,
      l.val = ((w.take j.val).flatMap (splitDart a b c)).length + k.val ∧
      (w.flatMap (splitDart a b c)).get l = (splitDart a b c (w.get j)).get k ∧
      splitWordChart w a b c (wordPoint w j t) =
        wordPoint (w.flatMap (splitDart a b c)) l s := by
  obtain ⟨hl, hget⟩ := flatMap_get_at w (splitDart a b c) j k
  refine ⟨⟨_, hl⟩, rfl, hget, ?_⟩
  apply Subtype.ext
  rw [splitWordChart_spec w a b c j ht, ha]
  change _ = (Circle.exp (2 * Real.pi *
    (((((w.take j.val).flatMap (splitDart a b c)).length + k.val : ℕ) : ℝ) +
      dartParameter ((w.flatMap (splitDart a b c)).get ⟨_, hl⟩) s) / _) : ℂ)
  rw [show (w.flatMap (splitDart a b c)).get ⟨_, hl⟩ =
    (splitDart a b c (w.get j)).get k from hget, Nat.cast_add, add_assoc]

private theorem splitWordChart_forward (w : Word) (a b c : ℕ) (j : Fin w.length)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ l : Fin (w.flatMap (splitDart a b c)).length, ∃ s ∈ Icc (0 : ℝ) 1,
      (((w.flatMap (splitDart a b c)).get l).1, s) = splitTarget a b c (w.get j).1 t ∧
      splitWordChart w a b c (wordPoint w j t) =
        wordPoint (w.flatMap (splitDart a b c)) l s := by
  obtain ⟨k, s, hs, hp, ha⟩ := splitDart_forward a b c (w.get j) ht
  obtain ⟨l, _, hget, hH⟩ := splitWordChart_side w a b c j k ht ha
  exact ⟨l, s, hs, hget ▸ hp, hH⟩

private theorem splitWordChart_backward (w : Word) (a b c : ℕ)
    (l : Fin (w.flatMap (splitDart a b c)).length) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ j : Fin w.length, ∃ t ∈ Icc (0 : ℝ) 1,
      splitParameter a b c (w.get j).1 t ((w.flatMap (splitDart a b c)).get l).1 s ∧
      splitWordChart w a b c (wordPoint w j t) =
        wordPoint (w.flatMap (splitDart a b c)) l s := by
  obtain ⟨j, k, hl⟩ := flatMap_index w (splitDart a b c) l
  obtain ⟨t, ht, hp, ha⟩ := splitDart_backward a b c (w.get j) k hs
  obtain ⟨l', hl', hget, hH⟩ := splitWordChart_side w a b c j k ht ha
  have heq : l' = l := Fin.ext (hl'.trans hl.symm)
  subst l'
  exact ⟨j, t, ht, hget ▸ hp, hH⟩

/-- The simultaneous subdivision of all occurrences of an edge is realized
by the radial extension of the piecewise linear boundary reparameterization.
Source: Gallier–Xu Definition 6.3(P1), p.84, and Note F.4, p.167. Each old
side receives one angular interval, or two when its label is subdivided;
the two new sides use the prescribed half-interval parameters. -/
theorem edge_subdivision_realized (P : Presentation) (a b c : ℕ)
    (ha : a ∈ labels P) (hb : b ∉ labels P) (hc : c ∉ labels P) (hbc : b ≠ c) :
    ∃ H : Realization P ≃ₜ Realization (subdivideEdge P a b c),
      RespectsParameters (.edge P a b c ha hb hc hbc) H := by
  let Q := subdivideEdge P a b c
  have hlen : P.length = Q.length := by simp [Q, subdivideEdge]
  let f : Fin P.length ≃ Fin Q.length := finCongr hlen
  have hword (i : Fin P.length) : Q.get (f i) = (P.get i).flatMap (splitDart a b c) := by
    simp only [Q, f, subdivideEdge, List.get_eq_getElem, List.getElem_map,
      ]
    rfl
  let F : FaceDisks P ≃ₜ FaceDisks Q :=
    { toFun := fun x ↦ (f x.1, splitWordChart (P.get x.1) a b c x.2)
      invFun := fun x ↦ (f.symm x.1, (splitWordChart (P.get (f.symm x.1)) a b c).symm x.2)
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      continuous_toFun := by
        change Continuous (fun x : Fin P.length × Disk ↦
          (f x.1, splitWordChart (P.get x.1) a b c x.2))
        apply continuous_prod_of_discrete_left.mpr
        intro i
        exact (continuous_const : Continuous (fun _ : Disk ↦ f i)).prodMk
          (splitWordChart (P.get i) a b c).continuous
      continuous_invFun := by
        change Continuous (fun x : Fin Q.length × Disk ↦
          (f.symm x.1, (splitWordChart (P.get (f.symm x.1)) a b c).symm x.2))
        apply continuous_prod_of_discrete_left.mpr
        intro i
        exact (continuous_const : Continuous (fun _ : Disk ↦ f.symm i)).prodMk
          (splitWordChart (P.get (f.symm i)) a b c).symm.continuous }
  have hforward (x : FaceDisks P) (i : Fin (P.get x.1).length) (t : ℝ)
      (ht : t ∈ Icc (0 : ℝ) 1) (hx : (x.2 : ℂ) = sidePoint P x.1 i t) :
      ∃ j : Fin (Q.get (F x).1).length, ∃ s ∈ Icc (0 : ℝ) 1,
        (((Q.get (F x).1).get j).1, s) = splitTarget a b c ((P.get x.1).get i).1 t ∧
        ((F x).2 : ℂ) = sidePoint Q (F x).1 j s := by
    change ∃ j : Fin (Q.get (f x.1)).length, ∃ s ∈ Icc (0 : ℝ) 1,
      (((Q.get (f x.1)).get j).1, s) = splitTarget a b c ((P.get x.1).get i).1 t ∧
      (splitWordChart (P.get x.1) a b c x.2 : ℂ) = sidePoint Q (f x.1) j s
    simp only [sidePoint]
    rw [hword]
    obtain ⟨j, s, hs, hp, hH⟩ := splitWordChart_forward (P.get x.1) a b c i ht
    have hx' : x.2 = wordPoint (P.get x.1) i t := Subtype.ext hx
    refine ⟨j, s, hs, hp, ?_⟩
    rw [hx', hH]
    rfl
  have hback (x : FaceDisks P) : ∀ (j : Fin (Q.get (F x).1).length) (s : ℝ),
      s ∈ Icc (0 : ℝ) 1 → ((F x).2 : ℂ) = sidePoint Q (F x).1 j s →
      ∃ i : Fin (P.get x.1).length, ∃ t ∈ Icc (0 : ℝ) 1,
        splitParameter a b c ((P.get x.1).get i).1 t ((Q.get (F x).1).get j).1 s ∧
        (x.2 : ℂ) = sidePoint P x.1 i t := by
    change ∀ (j : Fin (Q.get (f x.1)).length) (s : ℝ),
      s ∈ Icc (0 : ℝ) 1 → (splitWordChart (P.get x.1) a b c x.2 : ℂ) =
      sidePoint Q (f x.1) j s → ∃ i : Fin (P.get x.1).length,
      ∃ t ∈ Icc (0 : ℝ) 1,
        splitParameter a b c ((P.get x.1).get i).1 t ((Q.get (f x.1)).get j).1 s ∧
        (x.2 : ℂ) = sidePoint P x.1 i t
    simp only [sidePoint]
    rw [hword]
    intro j s hs hx
    obtain ⟨i, t, ht, hp, hH⟩ := splitWordChart_backward (P.get x.1) a b c j hs
    refine ⟨i, t, ht, hp, ?_⟩
    have hx' : splitWordChart (P.get x.1) a b c x.2 =
        wordPoint ((P.get x.1).flatMap (splitDart a b c)) j s := Subtype.ext hx
    have heq := (splitWordChart (P.get x.1) a b c).injective (hx'.trans hH.symm)
    exact congrArg Subtype.val heq
  have hfresh (x : FaceDisks P) (i : Fin (P.get x.1).length) :
      ((P.get x.1).get i).1 ≠ b ∧ ((P.get x.1).get i).1 ≠ c := by
    have hm : ((P.get x.1).get i).1 ∈ labels P := by
      simp only [labels, occurrences, List.mem_toFinset, List.mem_map, List.mem_flatten]
      exact ⟨_, ⟨P.get x.1, List.get_mem P x.1, List.get_mem _ i⟩, rfl⟩
    exact ⟨fun h ↦ hb (h ▸ hm), fun h ↦ hc (h ▸ hm)⟩
  have hedge (x y : FaceDisks P) :
      edgeIdentification P x y ↔ edgeIdentification Q (F x) (F y) := by
    constructor
    · rintro ⟨i, j, t, ht, hij, hx, hy⟩
      obtain ⟨i', s, hs, hp, hFx⟩ := hforward x i t ht hx
      obtain ⟨j', s', hs', hp', hFy⟩ := hforward y j t ht hy
      have he : (((Q.get (F x).1).get i').1, s) =
          (((Q.get (F y).1).get j').1, s') := hp.trans ((hij ▸ hp').symm)
      have hsval : s = s' := congrArg Prod.snd he
      subst s'
      exact ⟨i', j', s, hs, congrArg (fun z : ℕ × ℝ ↦ z.1) he, hFx, hFy⟩
    · rintro ⟨i, j, s, hs, hij, hx, hy⟩
      obtain ⟨i', t, ht, hp, hx'⟩ := hback x i s hs hx
      obtain ⟨j', t', ht', hp', hy'⟩ := hback y j s hs hy
      have he := splitParameter_injective (hfresh x i').1 (hfresh x i').2
        (hfresh y j').1 (hfresh y j').2 hbc hp (hij ▸ hp')
      rcases he with ⟨he, rfl⟩
      exact ⟨i', j', t, ht, he, hx', hy'⟩
  have hrel (x y : FaceDisks P) :
      Relation.EqvGen (edgeIdentification P) x y ↔
        Relation.EqvGen (edgeIdentification Q) (F x) (F y) := by
    constructor
    · intro hxy
      induction hxy with
      | rel a b hab => exact .rel _ _ ((hedge a b).mp hab)
      | refl a => exact .refl _
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'
    · intro hxy
      have hh : ∀ a b, Relation.EqvGen (edgeIdentification Q) a b →
          Relation.EqvGen (edgeIdentification P) (F.symm a) (F.symm b) := by
        intro a b hab
        induction hab with
        | rel a b hab =>
          apply Relation.EqvGen.rel
          apply (hedge _ _).mpr
          simpa only [F.apply_symm_apply] using hab
        | refl a => exact .refl _
        | symm _ _ _ ih => exact ih.symm
        | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'
      simpa only [F.symm_apply_apply] using hh _ _ hxy
  let H : Realization P ≃ₜ Realization Q := Homeomorph.Quotient.congr F hrel
  refine ⟨H, ?_⟩
  intro x y i j t s ht hs hp hx hy
  change splitParameter a b c ((P.get x.1).get i).1 t ((Q.get y.1).get j).1 s at hp
  have hy' : ((F (F.symm y)).2 : ℂ) = sidePoint Q (F (F.symm y)).1
      (finCongr (congrArg (fun z : FaceDisks Q ↦ (Q.get z.1).length)
        (F.apply_symm_apply y).symm) j) s := by
    simp only [F.apply_symm_apply, finCongr_apply]
    exact hy
  obtain ⟨k, r, hr, hparam, hk⟩ := hback (F.symm y) _ s hs hy'
  simp only [ finCongr_apply] at hparam
  have he := splitParameter_injective (hfresh x i).1 (hfresh x i).2
    (hfresh (F.symm y) k).1 (hfresh (F.symm y) k).2 hbc hp hparam
  rcases he with ⟨he, rfl⟩
  change project Q (F x) = project Q y
  apply Quotient.sound
  change Relation.EqvGen (edgeIdentification Q) (F x) y
  simpa only [F.apply_symm_apply] using (hrel x (F.symm y)).mp
    (Relation.EqvGen.rel _ _ ⟨i, k, t, ht, he, hx, hk⟩)

private def squareLoop (t : ℝ) : ℂ :=
  if t ≤ 1 then (t : ℂ) else if t ≤ 2 then 1 + (t - 1 : ℝ) * Complex.I
  else if t ≤ 3 then (3 - t : ℝ) + Complex.I else (4 - t : ℝ) * Complex.I

private theorem squareLoop_continuous : Continuous squareLoop := by
  unfold squareLoop
  refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const ?_
  · refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const ?_
    · apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
      intro x hx
      change x = 3 at hx
      subst x
      norm_num
    · intro x hx
      change x = 2 at hx
      subst x
      norm_num
  · intro x hx
    change x = 1 at hx
    subst x
    norm_num

private theorem squareLoop_end : squareLoop 0 = squareLoop 4 := by
  norm_num [squareLoop]

private theorem squareLoop_injective : InjOn squareLoop (Ico 0 4) := by
  intro s hs t ht h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [squareLoop] at hr hi
  split_ifs at hr hi <;> simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im,
    Complex.one_re, Complex.one_im, mul_zero, sub_zero, mul_one, zero_add,
    add_zero] at hr hi <;>
    rcases hs with ⟨hs0, hs4⟩ <;> rcases ht with ⟨ht0, ht4⟩ <;> linarith

private def squareRegion : Set ℂ := {z | z.re ∈ Icc (0 : ℝ) 1 ∧ z.im ∈ Icc (0 : ℝ) 1}

private theorem squareRegion_closed : IsClosed squareRegion :=
  (isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Icc.preimage Complex.continuous_im)

private theorem squareRegion_convex : Convex ℝ squareRegion :=
  ((convex_Icc (0 : ℝ) 1).is_linear_preimage Complex.reLm.isLinear).inter
    ((convex_Icc (0 : ℝ) 1).is_linear_preimage Complex.imLm.isLinear)

private theorem squareRegion_bounded : Bornology.IsBounded squareRegion := by
  apply (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr
  refine ⟨2, fun z hz ↦ ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
       _ ≤ 2 := by rw [abs_of_nonneg hz.1.1, abs_of_nonneg hz.2.1]; linarith [hz.1.2, hz.2.2]

private theorem squareRegion_interior : interior squareRegion =
    {z | z.re ∈ Ioo (0 : ℝ) 1 ∧ z.im ∈ Ioo (0 : ℝ) 1} := by
  change interior ((Complex.re ⁻¹' Icc 0 1) ∩ (Complex.im ⁻¹' Icc 0 1)) = _
  rw [interior_inter, Complex.interior_preimage_re, Complex.interior_preimage_im,
    interior_Icc]
  rfl

private theorem squareRegion_frontier : frontier squareRegion =
    {z | z ∈ squareRegion ∧ (z.re = 0 ∨ z.re = 1 ∨ z.im = 0 ∨ z.im = 1)} := by
  rw [frontier, squareRegion_closed.closure_eq, squareRegion_interior]
  ext z
  change (z ∈ squareRegion ∧ ¬(z.re ∈ Ioo (0 : ℝ) 1 ∧ z.im ∈ Ioo (0 : ℝ) 1)) ↔ _
  simp only [squareRegion, mem_ofPred_eq, mem_Icc, mem_Ioo]
  grind

private theorem squareLoop_image : squareLoop '' Icc 0 4 = frontier squareRegion := by
  rw [squareRegion_frontier]
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    unfold squareLoop
    split_ifs <;> simp only [squareRegion, mem_ofPred_eq, mem_Icc, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      Complex.add_im, Complex.mul_im, Complex.one_re, Complex.one_im,
      mul_zero, sub_zero, mul_one, zero_add, add_zero]
    all_goals refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
    all_goals solve | linarith [ht.1, ht.2] | simp
  · rintro ⟨hz, h | h | h | h⟩
    · refine ⟨4 - z.im, ⟨by linarith [hz.2.2], by linarith [hz.2.1]⟩, ?_⟩
      apply Complex.ext <;> simp only [squareLoop] <;> split_ifs <;>
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im,
          Complex.one_re, Complex.one_im, mul_zero, sub_zero, mul_one,
          zero_add, add_zero] <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
    · refine ⟨z.im + 1, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩, ?_⟩
      apply Complex.ext <;> simp only [squareLoop] <;> split_ifs <;>
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im,
          Complex.one_re, Complex.one_im, mul_zero, sub_zero, mul_one,
          zero_add, add_zero] <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
    · refine ⟨z.re, ⟨hz.1.1, by linarith [hz.1.2]⟩, ?_⟩
      have hr : z.re ≤ 1 := hz.1.2
      simp only [squareLoop, ite_eq_left hr]
      apply Complex.ext <;> simp [h]
    · refine ⟨3 - z.re, ⟨by linarith [hz.1.2], by linarith [hz.1.1]⟩, ?_⟩
      apply Complex.ext <;> simp only [squareLoop] <;> split_ifs <;>
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im,
          Complex.one_re, Complex.one_im, mul_zero, sub_zero, mul_one,
          zero_add, add_zero] <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]

private theorem square_boundary_parameter :
    ∃ j : Circle ≃ₜ frontier squareRegion,
      ∀ t ∈ Icc (0 : ℝ) 4,
        (j (Circle.exp (2*Real.pi*t/4))).val = squareLoop t := by
  have : Fact (0 < (4 : ℝ)) := ⟨by norm_num⟩
  let g : AddCircle (4 : ℝ) → ℂ := AddCircle.liftIco 4 0 squareLoop
  have hg : Continuous g := AddCircle.liftIco_zero_continuous
    squareLoop_end squareLoop_continuous.continuousOn
  have hginj : Function.Injective g := by
    intro a b hab
    apply (AddCircle.equivIco (4 : ℝ) 0).injective
    apply Subtype.ext
    exact squareLoop_injective (by simpa using (AddCircle.equivIco (4 : ℝ) 0 a).property)
      (by simpa using (AddCircle.equivIco (4 : ℝ) 0 b).property) hab
  let e : AddCircle (4 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle (by norm_num)
  let j : Circle → ℂ := g ∘ e.symm
  have hj : _root_.Topology.IsEmbedding j :=
    ((hg.comp e.symm.continuous).isClosedEmbedding (hginj.comp e.symm.injective)).isEmbedding
  have hformula (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) :
      j (Circle.exp (2*Real.pi*t/4)) = squareLoop t := by
    have he : Circle.exp (2*Real.pi*t/4) = e (t : AddCircle (4 : ℝ)) := by
      rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
      congr 1
      ring
    rw [he]
    change g (e.symm (e (t : AddCircle (4 : ℝ)))) = _
    rw [e.symm_apply_apply]
    by_cases h : t = 4
    · subst t
      change AddCircle.liftIco 4 0 squareLoop (4 : ℝ) = _
      rw [AddCircle.coe_period]
      rw [← squareLoop_end]
      exact AddCircle.liftIco_zero_coe_apply (by norm_num : (0 : ℝ) ∈ Ico 0 4)
    · exact AddCircle.liftIco_zero_coe_apply ⟨ht.1, lt_of_le_of_ne ht.2 h⟩
  have hrange : range j = frontier squareRegion := by
    rw [← squareLoop_image]
    apply Set.Subset.antisymm
    · rintro _ ⟨z, rfl⟩
      refine ⟨(AddCircle.equivIco (4 : ℝ) 0 (e.symm z)).val, ?_, rfl⟩
      simpa using Ico_subset_Icc_self (AddCircle.equivIco (4 : ℝ) 0 (e.symm z)).property
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨Circle.exp (2*Real.pi*t/4), hformula t ht⟩
  exact ⟨hj.toHomeomorph.trans (Homeomorph.setCongr hrange), hformula⟩

/-- A round disk chart on the square can prescribe the unit-speed
boundary traversal of its four sides. Source: Gallier–Xu Proposition 3.2 and
its prescribed-boundary remark, p.31; Note F.4 p.167. -/
private theorem square_disk_parameter :
    ∃ h : Metric.closedBall (0 : ℂ) 1 ≃ₜ squareRegion,
      ∀ t ∈ Icc (0 : ℝ) 4,
        (h ⟨Circle.exp (2*Real.pi*t/4), by exact sphere_subset_closedBall (Circle.exp _).property⟩).val = squareLoop t := by
  have hne : (interior squareRegion).Nonempty := by
    rw [squareRegion_interior]
    exact ⟨(1/2 : ℝ) + (1/2 : ℝ)*Complex.I, by norm_num⟩
  obtain ⟨H, _, hcl, hfr⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    squareRegion_convex hne squareRegion_bounded
  rw [squareRegion_closed.closure_eq] at hcl
  let H₀ : squareRegion ≃ₜ Metric.closedBall (0 : ℂ) 1 :=
    (H.image squareRegion).trans (Homeomorph.setCongr hcl)
  have hbd : ∀ z : squareRegion, z.val ∈ frontier squareRegion ↔ ‖(H₀ z : ℂ)‖ = 1 := by
    intro z
    change z.val ∈ frontier squareRegion ↔ ‖H z.val‖ = 1
    have hm : H z.val ∈ sphere (0 : ℂ) 1 ↔ ‖H z.val‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
    rw [← hm, ← hfr]
    exact H.injective.mem_set_image.symm
  obtain ⟨j, hj⟩ := square_boundary_parameter
  have hsubset : frontier squareRegion ⊆ squareRegion := by
    exact frontier_subset_closure.trans_eq squareRegion_closed.closure_eq
  obtain ⟨F, hF⟩ := HolomorphicAnosov.disk_prescribed_boundary_extension
    (frontier squareRegion) squareRegion hsubset H₀ hbd j.symm
  refine ⟨F.symm, ?_⟩
  intro t ht
  let z : frontier squareRegion := j (Circle.exp (2*Real.pi*t/4))
  have hz := hF z (hsubset z.property)
  have he : F ⟨z.val, hsubset z.property⟩ =
      ⟨Circle.exp (2*Real.pi*t/4), by exact sphere_subset_closedBall (Circle.exp _).property⟩ := by
    apply Subtype.ext
    exact hz.trans (congrArg Subtype.val (j.symm_apply_apply _))
  rw [← he, F.symm_apply_apply]
  exact hj t ht

private def squareLower : Set ℂ := {z | 0 ≤ z.im ∧ z.im ≤ z.re ∧ z.re ≤ 1}
private def squareUpper : Set ℂ := {z | 0 ≤ z.re ∧ z.re ≤ z.im ∧ z.im ≤ 1}

private def lowerAffine (z : ℂ) : ℂ := ⟨z.re + z.im, z.im⟩
private def upperAffine (z : ℂ) : ℂ := ⟨1 - z.re - z.im, 1 - z.im⟩

private def triangleLower : planarTriangle ≃ₜ squareLower where
  toFun z := ⟨lowerAffine z, ⟨z.property.2.1, by dsimp [lowerAffine]; linarith [z.property.1],
    z.property.2.2⟩⟩
  invFun z := ⟨⟨z.val.re - z.val.im, z.val.im⟩,
    ⟨by dsimp; linarith [z.property.2.1], z.property.1,
      by dsimp; linarith [z.property.2.2]⟩⟩
  left_inv z := by apply Subtype.ext; apply Complex.ext <;> dsimp [lowerAffine]; ring
  right_inv z := by apply Subtype.ext; apply Complex.ext <;> dsimp [lowerAffine]; ring
  continuous_toFun := by apply Continuous.subtype_mk; unfold lowerAffine; simp only [Complex.mk_eq_add_mul_I]; fun_prop
  continuous_invFun := by apply Continuous.subtype_mk; simp only [Complex.mk_eq_add_mul_I]; fun_prop

private def triangleUpper : planarTriangle ≃ₜ squareUpper where
  toFun z := ⟨upperAffine z,
    ⟨by dsimp [upperAffine]; linarith [z.property.2.2],
      by dsimp [upperAffine]; linarith [z.property.1],
      by dsimp [upperAffine]; linarith [z.property.2.1]⟩⟩
  invFun z := ⟨⟨z.val.im - z.val.re, 1 - z.val.im⟩,
    ⟨by dsimp; linarith [z.property.2.1],
      by dsimp; linarith [z.property.2.2], by dsimp; linarith [z.property.1]⟩⟩
  left_inv z := by apply Subtype.ext; apply Complex.ext <;> dsimp [upperAffine] <;> ring
  right_inv z := by apply Subtype.ext; apply Complex.ext <;> dsimp [upperAffine] <;> ring
  continuous_toFun := by apply Continuous.subtype_mk; unfold upperAffine; simp only [Complex.mk_eq_add_mul_I]; fun_prop
  continuous_invFun := by apply Continuous.subtype_mk; simp only [Complex.mk_eq_add_mul_I]; fun_prop

private theorem square_halves : squareLower ∪ squareUpper = squareRegion := by
  ext z
  simp only [squareLower, squareUpper, squareRegion, mem_union, mem_ofPred_eq, mem_Icc]
  constructor
  · rintro (h | h) <;> constructor <;> constructor <;> linarith [h.1, h.2.1, h.2.2]
  · rintro ⟨hr, hi⟩
    rcases le_total z.im z.re with h | h
    · exact Or.inl ⟨hi.1, h, hr.2⟩
    · exact Or.inr ⟨hr.1, h, hi.2⟩

private theorem square_halves_inter : squareLower ∩ squareUpper =
    {z | ∃ t ∈ Icc (0 : ℝ) 1, z = ⟨t, t⟩} := by
  ext z
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨z.re, ⟨hu.1, hl.2.2⟩, Complex.ext rfl (le_antisymm hl.2.1 hu.2.1)⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨ht.1, le_refl _, ht.2⟩, ⟨ht.1, le_refl _, ht.2⟩⟩

private theorem lowerAffine_loop {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    lowerAffine (planarTriangleLoop t) = squareLoop t := by
  apply Complex.ext <;> simp only [lowerAffine, planarTriangleLoop, squareLoop] <;>
    split_ifs <;> simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im,
      Complex.one_re, Complex.one_im, mul_zero, sub_zero, mul_one,
      zero_add, add_zero] <;> linarith [ht.1, ht.2]

private theorem upperAffine_loop {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    upperAffine (planarTriangleLoop t) = squareLoop (2 + t) := by
  apply Complex.ext <;> simp only [upperAffine, planarTriangleLoop, squareLoop] <;>
    split_ifs <;> simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im,
      Complex.one_re, Complex.one_im, mul_zero, sub_zero, mul_one,
      zero_add, add_zero] <;> linarith [ht.1, ht.2]

private theorem lowerAffine_seam {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    lowerAffine (planarTriangleLoop (2 + t)) = ⟨1 - t, 1 - t⟩ := by
  apply Complex.ext <;> simp only [lowerAffine, planarTriangleLoop] <;>
    split_ifs <;> simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im,
      mul_zero, sub_zero, mul_one, zero_add, add_zero] <;> linarith [ht.1, ht.2]

private theorem upperAffine_seam {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    upperAffine (planarTriangleLoop (3 - t)) = ⟨1 - t, 1 - t⟩ := by
  apply Complex.ext <;> simp only [upperAffine, planarTriangleLoop] <;>
    split_ifs <;> simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im,
      mul_zero, sub_zero, mul_one, zero_add, add_zero] <;> linarith [ht.1, ht.2]

private def diskAngle (t : ℝ) : Disk :=
  ⟨Circle.exp (2 * Real.pi * t), by rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩

private theorem bend_disk {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hb : b ∈ Ioo (0 : ℝ) 1) :
    ∃ H : Disk ≃ₜ Disk, ∀ t ∈ Icc (0 : ℝ) 1,
      H (diskAngle t) = diskAngle (angularBend a b t) := by
  obtain ⟨H, hH⟩ := interval_reparameterization_disk (angularBendOrderIso ha hb)
  refine ⟨H, fun t ht ↦ Subtype.ext ?_⟩
  exact hH ⟨t, by simpa using ht⟩

private theorem bend_chart {X : Type*} [TopologicalSpace X] (val : X → ℂ)
    (loop : ℝ → ℂ) {L : ℝ} (hL : 0 < L) (H : Disk ≃ₜ X)
    (hH : ∀ t ∈ Icc (0 : ℝ) L,
      val (H ⟨Circle.exp (2 * Real.pi * t / L), by
        rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩) = loop t)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    ∃ F : Disk ≃ₜ X, ∀ t ∈ Icc (0 : ℝ) 1,
      val (F (diskAngle t)) = loop (L * angularBend a b t) := by
  obtain ⟨B, hB⟩ := bend_disk ha hb
  refine ⟨B.trans H, ?_⟩
  intro t ht
  change val (H (B (diskAngle t))) = _
  rw [hB t ht]
  have hm := angularBend_mem ha hb ht
  have he : diskAngle (angularBend a b t) =
      ⟨Circle.exp (2 * Real.pi * (L * angularBend a b t) / L), by
        rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩ := by
    apply Subtype.ext
    dsimp only [diskAngle]
    congr 2
    field_simp
  rw [he]
  apply hH
  exact ⟨mul_nonneg hL.le hm.1, by nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hm.2)]⟩

private theorem square_cut_chart {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ H : Disk ≃ₜ squareRegion,
      (∀ t ∈ Icc (0 : ℝ) a, (H (diskAngle t) : ℂ) = squareLoop (2 * t / a)) ∧
      (∀ t ∈ Icc a 1, (H (diskAngle t) : ℂ) =
        squareLoop (2 + 2 * ((t - a) / (1 - a)))) := by
  obtain ⟨H, hH⟩ := square_disk_parameter
  obtain ⟨F, hF⟩ := bend_chart Subtype.val squareLoop (by norm_num : (0 : ℝ) < 4) H hH
    ha (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
  refine ⟨F, ?_, ?_⟩
  · intro t ht
    rw [hF t ⟨ht.1, ht.2.trans ha.2.le⟩]
    congr 1
    rw [angularBend, ite_eq_left ht.2]
    ring
  · intro t ht
    rw [hF t ⟨ha.1.le.trans ht.1, ht.2⟩]
    congr 1
    by_cases hta : t ≤ a
    · have he : t = a := le_antisymm hta ht.1
      subst t
      norm_num [angularBend, ne_of_gt ha.1]
    · rw [angularBend, ite_eq_right hta]
      ring

private theorem lower_cut_chart {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ H : Disk ≃ₜ squareLower,
      (∀ t ∈ Icc (0 : ℝ) a, (H (diskAngle t) : ℂ) = squareLoop (2 * t / a)) ∧
      (∀ t ∈ Icc a 1, (H (diskAngle t) : ℂ) =
        ⟨1 - (t - a) / (1 - a), 1 - (t - a) / (1 - a)⟩) := by
  obtain ⟨H, hH⟩ := planarTriangle_disk_parameter
  obtain ⟨F, hF⟩ := bend_chart Subtype.val planarTriangleLoop (by norm_num : (0 : ℝ) < 3) H hH
    ha (by norm_num : (2 / 3 : ℝ) ∈ Ioo 0 1)
  refine ⟨F.trans triangleLower, ?_, ?_⟩
  · intro t ht
    change lowerAffine (F (diskAngle t) : ℂ) = _
    rw [hF t ⟨ht.1, ht.2.trans ha.2.le⟩]
    have he : 3 * angularBend a (2 / 3) t = 2 * t / a := by
      rw [angularBend, ite_eq_left ht.2]
      ring
    rw [he, lowerAffine_loop]
    constructor
    · exact div_nonneg (mul_nonneg (by norm_num) ht.1) ha.1.le
    · rw [div_le_iff₀ ha.1]; linarith [ht.2]
  · intro t ht
    change lowerAffine (F (diskAngle t) : ℂ) = _
    rw [hF t ⟨ha.1.le.trans ht.1, ht.2⟩]
    have he : 3 * angularBend a (2 / 3) t = 2 + (t - a) / (1 - a) := by
      by_cases hta : t ≤ a
      · have he : t = a := le_antisymm hta ht.1
        subst t
        norm_num [angularBend, ne_of_gt ha.1]
      · rw [angularBend, ite_eq_right hta]; ring
    rw [he, lowerAffine_seam]
    exact ⟨div_nonneg (sub_nonneg.mpr ht.1) (by linarith [ha.2]),
      (div_le_one (by linarith [ha.2])).mpr (by linarith [ht.2])⟩

private theorem upper_cut_chart {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ H : Disk ≃ₜ squareUpper,
      (∀ t ∈ Icc (0 : ℝ) a, (H (diskAngle t) : ℂ) = squareLoop (2 + 2 * t / a)) ∧
      (∀ t ∈ Icc a 1, (H (diskAngle t) : ℂ) =
        ⟨(t - a) / (1 - a), (t - a) / (1 - a)⟩) := by
  obtain ⟨H, hH⟩ := planarTriangle_disk_parameter
  obtain ⟨F, hF⟩ := bend_chart Subtype.val planarTriangleLoop (by norm_num : (0 : ℝ) < 3) H hH
    ha (by norm_num : (2 / 3 : ℝ) ∈ Ioo 0 1)
  refine ⟨F.trans triangleUpper, ?_, ?_⟩
  · intro t ht
    change upperAffine (F (diskAngle t) : ℂ) = _
    rw [hF t ⟨ht.1, ht.2.trans ha.2.le⟩]
    have he : 3 * angularBend a (2 / 3) t = 2 * t / a := by
      rw [angularBend, ite_eq_left ht.2]
      ring
    rw [he, upperAffine_loop]
    constructor
    · exact div_nonneg (mul_nonneg (by norm_num) ht.1) ha.1.le
    · rw [div_le_iff₀ ha.1]; linarith [ht.2]
  · intro t ht
    change upperAffine (F (diskAngle t) : ℂ) = _
    rw [hF t ⟨ha.1.le.trans ht.1, ht.2⟩]
    have he : 3 * angularBend a (2 / 3) t = 3 - (1 - (t - a) / (1 - a)) := by
      by_cases hta : t ≤ a
      · have he : t = a := le_antisymm hta ht.1
        subst t
        norm_num [angularBend, ne_of_gt ha.1]
      · rw [angularBend, ite_eq_right hta]; ring
    rw [he, upperAffine_seam]
    · congr 1 <;> ring
    · have hq : (t - a) / (1 - a) ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (sub_nonneg.mpr ht.1) (by linarith [ha.2]),
          (div_le_one (by linarith [ha.2])).mpr (by linarith [ht.2])⟩
      exact ⟨by linarith [hq.2], by linarith [hq.1]⟩

private theorem quotient_homeomorph_of_quotient_map
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (rX : Setoid X) (rY : Setoid Y) (q : X → Y) (hq : IsQuotientMap q)
    (hr : ∀ x y, rX x y ↔ rY (q x) (q y)) :
    ∃ H : Quotient rX ≃ₜ Quotient rY, ∀ x,
      H (Quotient.mk rX x) = Quotient.mk rY (q x) := by
  let F : Quotient rX → Quotient rY := Quotient.map q (fun x y h ↦ (hr x y).mp h)
  have hF : Function.Bijective F := by
    constructor
    · intro x y hxy
      induction x using Quotient.inductionOn with | h x =>
        induction y using Quotient.inductionOn with | h y =>
          exact Quotient.sound ((hr x y).mpr (Quotient.exact hxy))
    · intro y
      induction y using Quotient.inductionOn with | h y =>
        obtain ⟨x, rfl⟩ := hq.surjective y
        exact ⟨Quotient.mk rX x, rfl⟩
  have hqc : IsQuotientMap F := by
    exact IsQuotientMap.of_comp_of_isCoinducing
      (f := Quotient.mk rX) (g := F)
      ((isQuotientMap_quotient_mk' (s := rY)).comp hq)
      (isQuotientMap_quotient_mk' (s := rX)).isCoinducing
  let e : Quotient rX ≃ Quotient rY := Equiv.ofBijective F hF
  have hi : Continuous e.symm := by
    apply hqc.continuous_iff.mpr
    have he : e.symm ∘ F = id := funext (fun x ↦ e.symm_apply_apply x)
    rw [he]
    exact continuous_id
  exact ⟨⟨e, hqc.continuous, hi⟩, fun _ ↦ rfl⟩

private theorem square_sum_quotient :
    IsQuotientMap (fun x : squareLower ⊕ squareUpper ↦
      (⟨Sum.elim Subtype.val Subtype.val x, by
        rw [← square_halves]
        cases x with
        | inl z => exact Or.inl z.property
        | inr z => exact Or.inr z.property⟩ : squareRegion)) := by
  let q : squareLower ⊕ squareUpper → squareRegion := fun x ↦
    ⟨Sum.elim Subtype.val Subtype.val x, by
      rw [← square_halves]
      cases x with
      | inl z => exact Or.inl z.property
      | inr z => exact Or.inr z.property⟩
  change IsQuotientMap q
  have hlow : IsClosed squareLower :=
    (isClosed_le continuous_const Complex.continuous_im).inter
      ((isClosed_le Complex.continuous_im Complex.continuous_re).inter
        (isClosed_le Complex.continuous_re continuous_const))
  have hupp : IsClosed squareUpper :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const))
  have hcompact : IsCompact squareRegion :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨squareRegion_closed, squareRegion_bounded⟩
  have hcl : IsCompact squareLower :=
    hcompact.of_isClosed_subset hlow (by intro z hz; rw [← square_halves]; exact Or.inl hz)
  have hcu : IsCompact squareUpper :=
    hcompact.of_isClosed_subset hupp (by intro z hz; rw [← square_halves]; exact Or.inr hz)
  let : CompactSpace squareLower := isCompact_iff_compactSpace.mp hcl
  let : CompactSpace squareUpper := isCompact_iff_compactSpace.mp hcu
  have hcont : Continuous q := by
    apply Continuous.subtype_mk
    exact continuous_sum_dom.mpr ⟨continuous_subtype_val, continuous_subtype_val⟩
  apply hcont.isClosedMap.isQuotientMap hcont
  intro z
  have hz : z.val ∈ squareLower ∪ squareUpper := square_halves.symm ▸ z.property
  rcases hz with hz | hz
  · exact ⟨Sum.inl ⟨z.val, hz⟩, rfl⟩
  · exact ⟨Sum.inr ⟨z.val, hz⟩, rfl⟩

private theorem eqvGen_quotient_pullback {X Y : Type*} (rX : X → X → Prop)
    (rY : Y → Y → Prop) (q : X → Y) (hq : Function.Surjective q)
    (hpush : ∀ x y, rX x y → Relation.EqvGen rY (q x) (q y))
    (hfiber : ∀ x y, q x = q y → Relation.EqvGen rX x y)
    (hlift : ∀ y z, rY y z → ∃ x w, q x = y ∧ q w = z ∧ Relation.EqvGen rX x w) :
    ∀ x w, Relation.EqvGen rX x w ↔ Relation.EqvGen rY (q x) (q w) := by
  have hback : ∀ y z, Relation.EqvGen rY y z →
      ∀ x w, q x = y → q w = z → Relation.EqvGen rX x w := by
    intro y z hyz
    induction hyz with
    | rel y z hyz =>
      obtain ⟨x', w', hx', hw', hrel⟩ := hlift y z hyz
      intro x w hx hw
      exact .trans _ _ _ (hfiber x x' (hx.trans hx'.symm))
        (.trans _ _ _ hrel (hfiber w' w (hw'.trans hw.symm)))
    | refl y => intro x w hx hw; exact hfiber x w (hx.trans hw.symm)
    | symm y z h ih => intro x w hx hw; exact (ih w x hw hx).symm
    | trans y z u h h' ih ih' =>
      intro x w hx hw
      obtain ⟨v, hv⟩ := hq z
      exact .trans _ _ _ (ih x v hx hv) (ih' v w hv hw)
  intro x w
  constructor
  · intro h
    induction h with
    | rel x w h => exact hpush x w h
    | refl x => exact .refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'
  · intro h
    exact hback _ _ h x w rfl rfl

private theorem diskAngle_period (t : ℝ) : diskAngle (t + 1) = diskAngle t := by
  apply Subtype.ext
  dsimp only [diskAngle]
  apply congrArg Subtype.val
  apply Circle.exp_eq_exp.mpr
  refine ⟨1, ?_⟩
  simp only [Int.cast_one]
  ring

private theorem diskAngle_zero_one : diskAngle 0 = diskAngle 1 := by
  simpa only [zero_add] using (diskAngle_period 0).symm

private theorem upper_cut_chart_rotated {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ H : Disk ≃ₜ squareUpper,
      (∀ t ∈ Icc (0 : ℝ) (1 - a), (H (diskAngle t) : ℂ) =
        ⟨t / (1 - a), t / (1 - a)⟩) ∧
      (∀ t ∈ Icc (1 - a) 1, (H (diskAngle t) : ℂ) =
        squareLoop (2 + 2 * (t - (1 - a)) / a)) := by
  obtain ⟨H, hH, hD⟩ := upper_cut_chart ha
  let R := diskRotation (2 * Real.pi * a)
  have hR (t : ℝ) : R (diskAngle t) = diskAngle (t + a) := by
    apply Subtype.ext
    change (Circle.exp (2 * Real.pi * a) : ℂ) * Circle.exp (2 * Real.pi * t) = _
    rw [← Circle.coe_mul, ← Circle.exp_add]
    congr 2
    ring
  refine ⟨R.trans H, ?_, ?_⟩
  · intro t ht
    change (H (R (diskAngle t)) : ℂ) = _
    rw [hR, hD (t + a) ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    congr 1 <;> ring
  · intro t ht
    change (H (R (diskAngle t)) : ℂ) = _
    rw [hR]
    have he : t + a = (t - (1 - a)) + 1 := by ring
    rw [he, diskAngle_period, hH (t - (1 - a)) ⟨by linarith [ht.1], by linarith [ht.2]⟩]

private theorem presentation_surgery {P Q : Presentation} (d : ℕ)
    (hd : d ∉ labels P) (q : FaceDisks Q → FaceDisks P) (hq : IsQuotientMap q)
    (hsurvive : ∀ y (j : Fin (Q.get y.1).length) s, s ∈ Icc (0 : ℝ) 1 →
      ((Q.get y.1).get j).1 ≠ d → (y.2 : ℂ) = sidePoint Q y.1 j s →
      ∃ i : Fin (P.get (q y).1).length,
        ((P.get (q y).1).get i).1 = ((Q.get y.1).get j).1 ∧
        ((q y).2 : ℂ) = sidePoint P (q y).1 i s)
    (hseam : ∀ x y (i : Fin (Q.get x.1).length) (j : Fin (Q.get y.1).length) s,
      s ∈ Icc (0 : ℝ) 1 → ((Q.get x.1).get i).1 = d → ((Q.get y.1).get j).1 = d →
      (x.2 : ℂ) = sidePoint Q x.1 i s → (y.2 : ℂ) = sidePoint Q y.1 j s → q x = q y)
    (hfiber : ∀ x y, q x = q y → Relation.EqvGen (edgeIdentification Q) x y)
    (hlift : ∀ x (i : Fin (P.get x.1).length) t, t ∈ Icc (0 : ℝ) 1 →
      (x.2 : ℂ) = sidePoint P x.1 i t →
      ∃ y : FaceDisks Q, ∃ j : Fin (Q.get y.1).length, q y = x ∧
        ((Q.get y.1).get j).1 = ((P.get x.1).get i).1 ∧
        (y.2 : ℂ) = sidePoint Q y.1 j t) :
    ∃ H : Realization P ≃ₜ Realization Q,
      ∀ x y (i : Fin (P.get x.1).length) (j : Fin (Q.get y.1).length) t,
        t ∈ Icc (0 : ℝ) 1 → ((P.get x.1).get i).1 = ((Q.get y.1).get j).1 →
        (x.2 : ℂ) = sidePoint P x.1 i t → (y.2 : ℂ) = sidePoint Q y.1 j t →
        H (project P x) = project Q y := by
  have hpush : ∀ x y, edgeIdentification Q x y →
      Relation.EqvGen (edgeIdentification P) (q x) (q y) := by
    rintro x y ⟨i, j, s, hs, he, hx, hy⟩
    by_cases hi : ((Q.get x.1).get i).1 = d
    · have hqxy := hseam x y i j s hs hi (he ▸ hi) hx hy
      rw [hqxy]
      exact .refl _
    · obtain ⟨i', hi', hx'⟩ := hsurvive x i s hs hi hx
      obtain ⟨j', hj', hy'⟩ := hsurvive y j s hs (he ▸ hi) hy
      exact .rel _ _ ⟨i', j', s, hs, hi'.trans (he.trans hj'.symm), hx', hy'⟩
  have hrlift : ∀ x y, edgeIdentification P x y →
      ∃ x' y', q x' = x ∧ q y' = y ∧ Relation.EqvGen (edgeIdentification Q) x' y' := by
    rintro x y ⟨i, j, t, ht, he, hx, hy⟩
    obtain ⟨x', i', hxq, hi, hx'⟩ := hlift x i t ht hx
    obtain ⟨y', j', hyq, hj, hy'⟩ := hlift y j t ht hy
    exact ⟨x', y', hxq, hyq,
      .rel _ _ ⟨i', j', t, ht, hi.trans (he.trans hj.symm), hx', hy'⟩⟩
  have hr := eqvGen_quotient_pullback (edgeIdentification Q) (edgeIdentification P)
    q hq.surjective hpush hfiber hrlift
  obtain ⟨H, hH⟩ := quotient_homeomorph_of_quotient_map
    (Relation.EqvGen.setoid (edgeIdentification Q))
    (Relation.EqvGen.setoid (edgeIdentification P)) q hq hr
  refine ⟨H.symm, ?_⟩
  intro x y i j t ht he hx hy
  have hne : ((Q.get y.1).get j).1 ≠ d := by
    intro h
    apply hd
    have hm : ((P.get x.1).get i).1 ∈ labels P := by
      simp only [labels, occurrences, List.mem_toFinset, List.mem_map, List.mem_flatten]
      exact ⟨_, ⟨P.get x.1, List.get_mem P x.1, List.get_mem _ i⟩, rfl⟩
    exact (he.trans h) ▸ hm
  obtain ⟨k, hk, hqy⟩ := hsurvive y j t ht hne hy
  apply H.injective
  rw [H.apply_symm_apply]
  change project P x = H (Quotient.mk _ y)
  rw [hH]
  exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨i, k, t, ht, he.trans hk.symm, hx, hqy⟩)

private structure FaceCutCharts (m n : ℕ) where
  old : Disk ≃ₜ squareRegion
  lower : Disk ≃ₜ squareLower
  upper : Disk ≃ₜ squareUpper
  old_left : ∀ r ∈ Icc (0 : ℝ) m,
    (old (diskAngle (r / (m + n))) : ℂ) = squareLoop (2 * r / m)
  old_right : ∀ r ∈ Icc (0 : ℝ) n,
    (old (diskAngle ((m + r) / (m + n))) : ℂ) = squareLoop (2 + 2 * r / n)
  lower_side : ∀ r ∈ Icc (0 : ℝ) m,
    (lower (diskAngle (r / (m + 1))) : ℂ) = squareLoop (2 * r / m)
  upper_side : ∀ r ∈ Icc (0 : ℝ) n,
    (upper (diskAngle ((1 + r) / (n + 1))) : ℂ) = squareLoop (2 + 2 * r / n)
  lower_seam : ∀ s ∈ Icc (0 : ℝ) 1,
    (lower (diskAngle ((m + s) / (m + 1))) : ℂ) = ⟨1 - s, 1 - s⟩
  upper_seam : ∀ s ∈ Icc (0 : ℝ) 1,
    (upper (diskAngle ((1 - s) / (n + 1))) : ℂ) = ⟨1 - s, 1 - s⟩

private theorem faceCutCharts_exists (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Nonempty (FaceCutCharts m n) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmn : (0 : ℝ) < m + n := add_pos hm' hn'
  have hm1 : (0 : ℝ) < m + 1 := by positivity
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have ha : (m : ℝ) / (m + n) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hm' hmn, (div_lt_one hmn).mpr (by linarith)⟩
  have hb : (m : ℝ) / (m + 1) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hm' hm1, (div_lt_one hm1).mpr (by linarith)⟩
  have hc : (n : ℝ) / (n + 1) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hn' hn1, (div_lt_one hn1).mpr (by linarith)⟩
  have hnfrac : 1 - (n : ℝ) / (n + 1) = 1 / (n + 1) := by field_simp; ring
  obtain ⟨O, hOl, hOr⟩ := square_cut_chart ha
  obtain ⟨L, hLs, hLd⟩ := lower_cut_chart hb
  obtain ⟨R, hRd, hRs⟩ := upper_cut_chart_rotated hc
  refine ⟨⟨O, L, R, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r hr
    rw [hOl _ ⟨div_nonneg hr.1 hmn.le, (div_le_div_iff_of_pos_right hmn).mpr hr.2⟩]
    congr 1
    field_simp
  · intro r hr
    have hr' : ((m : ℝ) + r) / (m + n) ∈ Icc ((m : ℝ) / (m + n)) 1 := by
      constructor
      · apply (div_le_div_iff_of_pos_right hmn).mpr
        linarith [hr.1]
      · apply (div_le_one hmn).mpr
        linarith [hr.2]
    rw [hOr _ hr']
    congr 1
    field_simp [ne_of_gt hm', ne_of_gt hn', ne_of_gt hmn]
    ring
  · intro r hr
    rw [hLs _ ⟨div_nonneg hr.1 hm1.le, (div_le_div_iff_of_pos_right hm1).mpr hr.2⟩]
    congr 1
    field_simp
  · intro r hr
    have hr' : (1 + r) / ((n : ℝ) + 1) ∈ Icc (1 - (n : ℝ) / (n + 1)) 1 := by
      rw [hnfrac]
      constructor
      · apply (div_le_div_iff_of_pos_right hn1).mpr
        linarith [hr.1]
      · apply (div_le_one hn1).mpr
        linarith [hr.2]
    rw [hRs _ hr', hnfrac]
    congr 1
    field_simp
    ring
  · intro r hr
    have hr' : ((m : ℝ) + r) / (m + 1) ∈ Icc ((m : ℝ) / (m + 1)) 1 := by
      constructor
      · apply (div_le_div_iff_of_pos_right hm1).mpr
        linarith [hr.1]
      · apply (div_le_one hm1).mpr
        linarith [hr.2]
    rw [hLd _ hr']
    have he : (((m : ℝ) + r) / (m + 1) - m / (m + 1)) / (1 - m / (m + 1)) = r := by
      field_simp
      ring
    rw [he]
  · intro r hr
    have hr' : (1 - r) / ((n : ℝ) + 1) ∈ Icc (0 : ℝ) (1 - (n : ℝ) / (n + 1)) := by
      rw [hnfrac]
      exact ⟨div_nonneg (by linarith [hr.2]) hn1.le,
        (div_le_div_iff_of_pos_right hn1).mpr (by linarith [hr.1])⟩
    rw [hRd _ hr', hnfrac]
    congr 1 <;> field_simp

private def appendIndex (L R : Presentation) :
    Fin L.length ⊕ Fin R.length ≃ Fin (L ++ R).length :=
  finSumFinEquiv.trans (finCongr (List.length_append (as := L) (bs := R)).symm)

private theorem appendIndex_left (L R : Presentation) (i : Fin L.length) :
    (L ++ R).get (appendIndex L R (.inl i)) = L.get i := by
  simp only [appendIndex, Equiv.trans_apply, finCongr_apply, List.get_eq_getElem,
    Fin.val_cast, finSumFinEquiv_apply_left, Fin.val_castAdd]
  exact List.getElem_append_left i.isLt

private theorem appendIndex_right (L R : Presentation) (i : Fin R.length) :
    (L ++ R).get (appendIndex L R (.inr i)) = R.get i := by
  simp only [appendIndex, Equiv.trans_apply, finCongr_apply, List.get_eq_getElem,
    Fin.val_cast, finSumFinEquiv_apply_right, Fin.val_natAdd]
  rw [List.getElem_append_right (by omega)]
  simp

private def tripleIndex (L M R : Presentation) :
    (Fin L.length ⊕ Fin M.length) ⊕ Fin R.length ≃ Fin (L ++ M ++ R).length :=
  (Equiv.sumCongr (appendIndex L M) (Equiv.refl _)).trans (appendIndex (L ++ M) R)

private theorem tripleIndex_word (L M R : Presentation)
    (i : (Fin L.length ⊕ Fin M.length) ⊕ Fin R.length) :
    (L ++ M ++ R).get (tripleIndex L M R i) = Sum.elim (Sum.elim L.get M.get) R.get i := by
  rcases i with (i | i) | i
  · exact (appendIndex_left (L ++ M) R _).trans (appendIndex_left L M i)
  · exact (appendIndex_left (L ++ M) R _).trans (appendIndex_right L M i)
  · exact appendIndex_right (L ++ M) R i

private def faceReindexDisk {I J : Type*} [TopologicalSpace I] [TopologicalSpace J]
    [DiscreteTopology I] [DiscreteTopology J] (e : I ≃ J) : I × Disk ≃ₜ J × Disk where
  toFun x := (e x.1, x.2)
  invFun x := (e.symm x.1, x.2)
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := (continuous_of_discreteTopology.comp continuous_fst).prodMk continuous_snd
  continuous_invFun := (continuous_of_discreteTopology.comp continuous_fst).prodMk continuous_snd

private def faceCutMap {m n : ℕ} (C : FaceCutCharts m n) : Disk ⊕ Disk → Disk :=
  Sum.elim
    (fun z ↦ C.old.symm ⟨C.lower z, by
      rw [← square_halves]; exact Or.inl (C.lower z).property⟩)
    (fun z ↦ C.old.symm ⟨C.upper z, by
      rw [← square_halves]; exact Or.inr (C.upper z).property⟩)

private theorem faceCutMap_quotient {m n : ℕ} (C : FaceCutCharts m n) :
    IsQuotientMap (faceCutMap C) := by
  let e : Disk ⊕ Disk ≃ₜ squareLower ⊕ squareUpper := C.lower.sumCongr C.upper
  have he : IsQuotientMap e := e.isQuotientMap
  have h := C.old.symm.isQuotientMap.comp (square_sum_quotient.comp he)
  convert h using 1
  funext x
  cases x <;> rfl

private theorem faceCutMap_fiber {m n : ℕ} (C : FaceCutCharts m n)
    (x y : Disk ⊕ Disk) (h : faceCutMap C x = faceCutMap C y) :
    x = y ∨ ∃ t ∈ Icc (0 : ℝ) 1,
      ((∃ u v : Disk, x = .inl u ∧ y = .inr v ∧
        u = diskAngle ((m + t) / (m + 1)) ∧ v = diskAngle ((1 - t) / (n + 1))) ∨
       (∃ u v : Disk, x = .inr v ∧ y = .inl u ∧
        u = diskAngle ((m + t) / (m + 1)) ∧ v = diskAngle ((1 - t) / (n + 1)))) := by
  have hcross (u v : Disk) (h : faceCutMap C (.inl u) = faceCutMap C (.inr v)) :
      ∃ t ∈ Icc (0 : ℝ) 1,
        u = diskAngle ((m + t) / (m + 1)) ∧ v = diskAngle ((1 - t) / (n + 1)) := by
    have hv : (C.lower u : ℂ) = (C.upper v : ℂ) :=
      congrArg Subtype.val (C.old.symm.injective h)
    have hm : (C.lower u : ℂ) ∈ squareLower ∩ squareUpper :=
      ⟨(C.lower u).property, hv ▸ (C.upper v).property⟩
    rw [square_halves_inter] at hm
    obtain ⟨s, hs, hxy⟩ := hm
    have ht : 1 - s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    refine ⟨1 - s, ht, ?_, ?_⟩
    · apply C.lower.injective
      apply Subtype.ext
      rw [C.lower_seam _ ht, hxy]
      congr 1 <;> ring
    · apply C.upper.injective
      apply Subtype.ext
      rw [C.upper_seam _ ht, ← hv, hxy]
      congr 1 <;> ring
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      left
      apply congrArg Sum.inl
      apply C.lower.injective
      exact Subtype.ext (congrArg (fun z : squareRegion ↦ z.val) (C.old.symm.injective h))
    | inr v =>
      obtain ⟨t, ht, hu, hv⟩ := hcross u v h
      exact Or.inr ⟨t, ht, Or.inl ⟨u, v, rfl, rfl, hu, hv⟩⟩
  | inr v =>
    cases y with
    | inl u =>
      obtain ⟨t, ht, hu, hv⟩ := hcross u v h.symm
      exact Or.inr ⟨t, ht, Or.inr ⟨u, v, rfl, rfl, hu, hv⟩⟩
    | inr u =>
      left
      apply congrArg Sum.inr
      apply C.upper.injective
      exact Subtype.ext (congrArg (fun z : squareRegion ↦ z.val) (C.old.symm.injective h))

private def twoDisk (i : Fin 2) (z : Disk) : Disk ⊕ Disk :=
  if i = 0 then .inl z else .inr z

private def cutTaggedMap (l r : ℕ) {m n : ℕ} (C : FaceCutCharts m n) :
    ((Fin l ⊕ Fin 2) ⊕ Fin r) × Disk → ((Fin l ⊕ Fin 1) ⊕ Fin r) × Disk :=
  fun x ↦ match x.1 with
  | .inl (.inl i) => (.inl (.inl i), x.2)
  | .inl (.inr i) => (.inl (.inr 0), faceCutMap C (twoDisk i x.2))
  | .inr i => (.inr i, x.2)

private theorem cutTaggedMap_quotient (l r : ℕ) {m n : ℕ} (C : FaceCutCharts m n) :
    IsQuotientMap (cutTaggedMap l r C) := by
  have hcont : Continuous (cutTaggedMap l r C) := by
    apply continuous_prod_of_discrete_left.mpr
    rintro ((i | i) | i)
    · exact (continuous_const : Continuous (fun _ : Disk ↦
        (Sum.inl (Sum.inl i) : (Fin l ⊕ Fin 1) ⊕ Fin r))).prodMk continuous_id
    · change Continuous (fun z ↦ ((Sum.inl (Sum.inr 0) : (Fin l ⊕ Fin 1) ⊕ Fin r),
        faceCutMap C (twoDisk i z)))
      apply continuous_const.prodMk
      unfold twoDisk
      split
      · exact (faceCutMap_quotient C).continuous.comp continuous_inl
      · exact (faceCutMap_quotient C).continuous.comp continuous_inr
    · exact (continuous_const : Continuous (fun _ : Disk ↦
        (Sum.inr i : (Fin l ⊕ Fin 1) ⊕ Fin r))).prodMk continuous_id
  apply hcont.isClosedMap.isQuotientMap hcont
  rintro ⟨(i | i) | i, z⟩
  · exact ⟨(.inl (.inl i), z), rfl⟩
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    obtain ⟨w, hw⟩ := (faceCutMap_quotient C).surjective z
    cases w with
    | inl w => exact ⟨(.inl (.inr 0), w), Prod.ext rfl hw⟩
    | inr w => exact ⟨(.inl (.inr 1), w), Prod.ext rfl hw⟩
  · exact ⟨(.inr i, z), rfl⟩

private def faceCutFullMap (L R : Presentation) (U V : Word) (d : ℕ)
    (C : FaceCutCharts U.length V.length) :
    FaceDisks (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R) →
      FaceDisks (L ++ [U ++ V] ++ R) :=
  (faceReindexDisk (tripleIndex L [U ++ V] R)) ∘
    cutTaggedMap L.length R.length C ∘
    (faceReindexDisk (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R)).symm

private theorem faceCutFullMap_quotient (L R : Presentation) (U V : Word) (d : ℕ)
    (C : FaceCutCharts U.length V.length) : IsQuotientMap (faceCutFullMap L R U V d C) :=
  (faceReindexDisk (tripleIndex L [U ++ V] R)).isQuotientMap.comp
    ((cutTaggedMap_quotient L.length R.length C).comp
      (faceReindexDisk (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R)).symm.isQuotientMap)

private theorem faceCutFullMap_apply (L R : Presentation) (U V : Word) (d : ℕ)
    (C : FaceCutCharts U.length V.length)
    (i : (Fin L.length ⊕ Fin 2) ⊕ Fin R.length) (z : Disk) :
    faceCutFullMap L R U V d C
      (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R i, z) =
      (faceReindexDisk (tripleIndex L [U ++ V] R)) (cutTaggedMap L.length R.length C (i, z)) := by
  simp [faceCutFullMap, faceReindexDisk, Homeomorph.symm]


private theorem faceCutMap_left_side {m n : ℕ} (C : FaceCutCharts m n) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) m) :
    faceCutMap C (.inl (diskAngle (r / (m + 1)))) = diskAngle (r / (m + n)) := by
  apply C.old.injective
  apply Subtype.ext
  change (C.old (C.old.symm _) : ℂ) = _
  rw [C.old.apply_symm_apply]
  exact (C.lower_side r hr).trans (C.old_left r hr).symm

private theorem faceCutMap_right_side {m n : ℕ} (C : FaceCutCharts m n) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) n) :
    faceCutMap C (.inr (diskAngle ((1 + r) / (n + 1)))) =
      diskAngle ((m + r) / (m + n)) := by
  apply C.old.injective
  apply Subtype.ext
  change (C.old (C.old.symm _) : ℂ) = _
  rw [C.old.apply_symm_apply]
  exact (C.upper_side r hr).trans (C.old_right r hr).symm

private theorem faceCutMap_seam {m n : ℕ} (C : FaceCutCharts m n) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    faceCutMap C (.inl (diskAngle ((m + t) / (m + 1)))) =
      faceCutMap C (.inr (diskAngle ((1 - t) / (n + 1)))) := by
  apply C.old.injective
  apply Subtype.ext
  change (C.old (C.old.symm _) : ℂ) = (C.old (C.old.symm _) : ℂ)
  simp only [C.old.apply_symm_apply]
  exact (C.lower_seam t ht).trans (C.upper_seam t ht).symm

private def cutTag {l r : ℕ} : (Fin l ⊕ Fin 2) ⊕ Fin r → (Fin l ⊕ Fin 1) ⊕ Fin r
  | .inl (.inl i) => .inl (.inl i)
  | .inl (.inr _) => .inl (.inr 0)
  | .inr i => .inr i

private theorem dartParameter_mem (d : Dart) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dartParameter d t ∈ Icc (0 : ℝ) 1 := by
  unfold dartParameter
  split
  · exact ht
  · exact ⟨by linarith [ht.2], by linarith [ht.1]⟩

private theorem faceCutFullMap_survives (L R : Presentation) (U V : Word) (d : ℕ)
    (C : FaceCutCharts U.length V.length)
    (tag : (Fin L.length ⊕ Fin 2) ⊕ Fin R.length) :
    ∀ (j : Fin ((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get
      (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R tag)).length) t,
      t ∈ Icc (0 : ℝ) 1 →
      (((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get
        (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R tag)).get j).1 ≠ d →
      ∃ i : Fin ((L ++ [U ++ V] ++ R).get (tripleIndex L [U ++ V] R (cutTag tag))).length,
        (((L ++ [U ++ V] ++ R).get (tripleIndex L [U ++ V] R (cutTag tag))).get i).1 =
          (((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get
            (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R tag)).get j).1 ∧
        faceCutFullMap L R U V d C
          (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R tag,
            wordPoint ((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get
              (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R tag)) j t) =
          (tripleIndex L [U ++ V] R (cutTag tag),
            wordPoint ((L ++ [U ++ V] ++ R).get
              (tripleIndex L [U ++ V] R (cutTag tag))) i t) := by
  simp only [faceCutFullMap_apply]
  rcases tag with (k | k) | k
  · rw [tripleIndex_word, tripleIndex_word]
    intro j t ht hj
    exact ⟨j, rfl, rfl⟩
  · fin_cases k
    · rw [tripleIndex_word, tripleIndex_word]
      simp only [Sum.elim_inl, Sum.elim_inr, cutTag, List.get_eq_getElem, Fin.val_mk,
        List.getElem_cons_zero]
      intro j t ht hj
      have hjU : j.val < U.length := by
        by_contra h
        have hjlen := j.isLt
        simp only [List.length_append, List.length_cons, List.length_nil] at hjlen
        have hjEq : j.val = U.length := by omega
        have he : ((U ++ [(d, true)]).get j).1 = d := by
          simp only [List.get_eq_getElem]
          rw [List.getElem_append_right (by omega)]
          simp [hjEq]
        exact hj he
      let i : Fin (U ++ V).length := ⟨j.val, by simp; omega⟩
      have hji : (U ++ [(d, true)]).get j = (U ++ V).get i := by
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_left hjU, List.getElem_append_left hjU]
      refine ⟨i, congrArg Prod.fst hji.symm, ?_⟩
      change (_, faceCutMap C (.inl (wordPoint (U ++ [(d, true)]) j t))) =
        (_, wordPoint (U ++ V) i t)
      apply Prod.ext (by rfl)
      have hpar := dartParameter_mem ((U ++ [(d, true)]).get j) ht
      have hr : (j.val : ℝ) + dartParameter ((U ++ [(d, true)]).get j) t ∈
          Icc (0 : ℝ) U.length := by
        constructor
        · exact add_nonneg (Nat.cast_nonneg _) hpar.1
        · have : (j.val : ℝ) + 1 ≤ U.length := by exact_mod_cast hjU
          linarith [hpar.2]
      have hz : wordPoint (U ++ [(d, true)]) j t =
          diskAngle ((j.val + dartParameter ((U ++ [(d, true)]).get j) t) / (U.length + 1)) := by
        apply Subtype.ext
        simp only [wordPoint, diskAngle, List.length_append, List.length_cons, List.length_nil,
          Nat.cast_add, Nat.cast_one, zero_add, mul_div_assoc]
      rw [hz, faceCutMap_left_side C hr]
      apply Subtype.ext
      simp only [diskAngle, wordPoint, List.length_append, Nat.cast_add, mul_div_assoc, hji]
      rfl
    · rw [tripleIndex_word, tripleIndex_word]
      simp only [Sum.elim_inl, Sum.elim_inr, cutTag, List.get_eq_getElem, Fin.val_mk,
        List.getElem_cons_zero, List.getElem_cons_succ]
      intro j t ht hj
      have hjpos : 0 < j.val := by
        by_contra h
        have hj0 : j.val = 0 := by omega
        apply hj
        simp [ hj0]
      have hjV : j.val - 1 < V.length := by have := j.isLt; simp only [List.length_cons] at this; omega
      let i : Fin (U ++ V).length := ⟨U.length + (j.val - 1), by simp; omega⟩
      have hji : ((d, false) :: V).get j = (U ++ V).get i := by
        simp only [List.get_eq_getElem]
        have hjE : j.val = (j.val - 1) + 1 := by omega
        rw [List.getElem_cons]
        rw [dite_eq_right (by omega)]
        rw [List.getElem_append_right (by dsimp [i]; omega)]
        simp [i]
      refine ⟨i, congrArg Prod.fst hji.symm, ?_⟩
      change (_, faceCutMap C (.inr (wordPoint ((d, false) :: V) j t))) =
        (_, wordPoint (U ++ V) i t)
      apply Prod.ext (by rfl)
      have hpar := dartParameter_mem (((d, false) :: V).get j) ht
      have hr : ((j.val - 1 : ℕ) : ℝ) + dartParameter (((d, false) :: V).get j) t ∈
          Icc (0 : ℝ) V.length := by
        constructor
        · exact add_nonneg (Nat.cast_nonneg _) hpar.1
        · have : ((j.val - 1 : ℕ) : ℝ) + 1 ≤ V.length := by exact_mod_cast hjV
          linarith [hpar.2]
      have hz : wordPoint ((d, false) :: V) j t =
          diskAngle ((1 + (((j.val - 1 : ℕ) : ℝ) +
            dartParameter (((d, false) :: V).get j) t)) / (V.length + 1)) := by
        apply Subtype.ext
        simp only [wordPoint, diskAngle, List.length_cons, Nat.cast_add, Nat.cast_one]
        congr 2
        have hjR : (j.val : ℝ) = 1 + ((j.val - 1 : ℕ) : ℝ) := by exact_mod_cast (show j.val = 1 + (j.val - 1) by omega)
        rw [hjR]
        ring
      rw [hz, faceCutMap_right_side C hr]
      apply Subtype.ext
      simp only [diskAngle, wordPoint, List.length_append, Nat.cast_add, i, hji]
      congr 2
      ring
  · rw [tripleIndex_word, tripleIndex_word]
    intro j t ht hj
    exact ⟨j, rfl, rfl⟩

private def lowerSeamPoint (L R : Presentation) (U V : Word) (d : ℕ) (t : ℝ) :
    FaceDisks (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R) :=
  (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R (.inl (.inr ⟨0, by simp⟩)),
    diskAngle ((U.length + t) / (U.length + 1)))

private def upperSeamPoint (L R : Presentation) (U V : Word) (d : ℕ) (t : ℝ) :
    FaceDisks (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R) :=
  (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R (.inl (.inr ⟨1, by simp⟩)),
    diskAngle ((1 - t) / (V.length + 1)))

private theorem faceCutFull_seam_relation (L R : Presentation) (U V : Word) (d : ℕ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    edgeIdentification (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R)
      (lowerSeamPoint L R U V d t) (upperSeamPoint L R U V d t) := by
  unfold edgeIdentification
  dsimp only [lowerSeamPoint, upperSeamPoint, Prod.fst, Prod.snd]
  simp only [sidePoint]
  rw [tripleIndex_word, tripleIndex_word]
  simp only [Sum.elim_inl, Sum.elim_inr, List.get_eq_getElem, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ]
  refine ⟨⟨U.length, by simp⟩, ⟨0, by simp⟩, t, ht, ?_, ?_, ?_⟩
  · simp
  · simp [diskAngle, mul_div_assoc]
  · simp [diskAngle, mul_div_assoc]

private theorem fresh_dart (P : Presentation) {d : ℕ} (hd : d ∉ labels P)
    {w : Word} (hw : w ∈ P) {a : Dart} (ha : a ∈ w) : a.1 ≠ d := by
  intro he
  apply hd
  simp only [labels, occurrences, List.mem_toFinset, List.mem_map, List.mem_flatten]
  exact ⟨a, ⟨w, hw, ha⟩, he⟩

private theorem faceCutFull_seam_point (L R : Presentation) (U V : Word) (d : ℕ)
    (hd : d ∉ labels (L ++ [U ++ V] ++ R))
    (tag : (Fin L.length ⊕ Fin 2) ⊕ Fin R.length) :
    ∀ (j : Fin ((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get
      (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R tag)).length) t,
      (((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get
        (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R tag)).get j).1 = d →
      (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R tag,
        wordPoint ((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get
          (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R tag)) j t) =
        lowerSeamPoint L R U V d t ∨
      (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R tag,
        wordPoint ((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get
          (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R tag)) j t) =
        upperSeamPoint L R U V d t := by
  have hUV : U ++ V ∈ L ++ [U ++ V] ++ R := by simp
  rcases tag with (k | k) | k
  · rw [tripleIndex_word]
    intro j t hj
    exact False.elim (fresh_dart _ hd (by simp []) (List.get_mem _ j) hj)
  · fin_cases k
    · rw [tripleIndex_word]
      simp only [Sum.elim_inl, Sum.elim_inr, List.get_eq_getElem, Fin.val_mk,
        List.getElem_cons_zero]
      intro j t hj
      have hjeq : j.val = U.length := by
        have hlen := j.isLt
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        by_contra hne
        have hjU : j.val < U.length := by omega
        apply fresh_dart _ hd hUV (List.mem_append_left _ (List.getElem_mem hjU))
        simpa only [List.getElem_append_left hjU] using hj
      left
      unfold lowerSeamPoint
      apply Prod.ext (by congr 2)
      apply Subtype.ext
      simp [wordPoint, diskAngle, dartParameter, hjeq, mul_div_assoc]
    · rw [tripleIndex_word]
      simp only [Sum.elim_inl, Sum.elim_inr, List.get_eq_getElem, Fin.val_mk,
        List.getElem_cons_zero, List.getElem_cons_succ]
      intro j t hj
      have hjeq : j.val = 0 := by
        by_contra hne
        have hjV : j.val - 1 < V.length := by have := j.isLt; simp at this; omega
        apply fresh_dart _ hd hUV (List.mem_append_right _ (List.getElem_mem hjV))
        simpa only [List.getElem_cons, dite_eq_right hne] using hj
      right
      unfold upperSeamPoint
      apply Prod.ext (by congr 2)
      apply Subtype.ext
      simp [wordPoint, diskAngle, dartParameter, hjeq, mul_div_assoc]
  · rw [tripleIndex_word]
    intro j t hj
    exact False.elim (fresh_dart _ hd (by simp []) (List.get_mem _ j) hj)

private theorem faceCutFullMap_fiber (L R : Presentation) (U V : Word) (d : ℕ)
    (C : FaceCutCharts U.length V.length)
    (x y : FaceDisks (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R))
    (h : faceCutFullMap L R U V d C x = faceCutFullMap L R U V d C y) :
    Relation.EqvGen (edgeIdentification (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R)) x y := by
  let e := tripleIndex L [U ++ [(d, true)], (d, false) :: V] R
  obtain ⟨i, hi⟩ := e.surjective x.1
  obtain ⟨j, hj⟩ := e.surjective y.1
  rcases x with ⟨x, z⟩
  rcases y with ⟨y, w⟩
  dsimp only at hi hj
  subst x y
  change faceCutFullMap _ _ _ _ _ _ (e i, z) = faceCutFullMap _ _ _ _ _ _ (e j, w) at h
  dsimp only [e] at h ⊢
  rw [faceCutFullMap_apply, faceCutFullMap_apply] at h
  have hh := (faceReindexDisk (tripleIndex L [U ++ V] R)).injective h
  have htag := congrArg Prod.fst hh
  have hval := congrArg Prod.snd hh
  rcases i with (i | i) | i <;> rcases j with (j | j) | j
  all_goals dsimp only [cutTaggedMap, Prod.fst, Prod.snd] at htag hval
  all_goals try { simp only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl] at htag }
  all_goals try { cases htag; cases hval; exact .refl _ }
  · have hmid : faceCutMap C (twoDisk i z) = faceCutMap C (twoDisk j w) := hval
    rcases faceCutMap_fiber C _ _ hmid with he | ⟨t, ht, he | he⟩
    · have hzw : (i, z) = (j, w) := by
        fin_cases i <;> fin_cases j <;> simp [twoDisk] at he ⊢ <;> exact he
      cases hzw
      exact .refl _
    · rcases he with ⟨u, v, hx, hy, hu, hv⟩
      have hi : i = 0 ∧ z = diskAngle ((U.length + t) / (U.length + 1)) := by
        fin_cases i <;> simp [twoDisk] at hx
        exact ⟨rfl, hx.trans hu⟩
      have hj : j = 1 ∧ w = diskAngle ((1 - t) / (V.length + 1)) := by
        fin_cases j <;> simp [twoDisk] at hy
        exact ⟨rfl, hy.trans hv⟩
      rcases hi with ⟨rfl, rfl⟩
      rcases hj with ⟨rfl, rfl⟩
      exact .rel _ _ (faceCutFull_seam_relation L R U V d ht)
    · rcases he with ⟨u, v, hx, hy, hu, hv⟩
      have hi : i = 1 ∧ z = diskAngle ((1 - t) / (V.length + 1)) := by
        fin_cases i <;> simp [twoDisk] at hx
        exact ⟨rfl, hx.trans hv⟩
      have hj : j = 0 ∧ w = diskAngle ((U.length + t) / (U.length + 1)) := by
        fin_cases j <;> simp [twoDisk] at hy
        exact ⟨rfl, hy.trans hu⟩
      rcases hi with ⟨rfl, rfl⟩
      rcases hj with ⟨rfl, rfl⟩
      exact (Relation.EqvGen.rel _ _ (faceCutFull_seam_relation L R U V d ht)).symm

private theorem wordPoint_cast {w v : Word} (h : w = v) (i : Fin v.length) (t : ℝ) :
    wordPoint w (finCongr (congrArg List.length h).symm i) t = wordPoint v i t := by
  subst v
  rfl

private theorem wordGet_cast {w v : Word} (h : w = v) (i : Fin v.length) :
    w.get (finCongr (congrArg List.length h).symm i) = v.get i := by
  subst v
  rfl

private theorem faceCutFullMap_lift (L R : Presentation) (U V : Word) (d : ℕ)
    (C : FaceCutCharts U.length V.length)
    (tag : (Fin L.length ⊕ Fin 1) ⊕ Fin R.length) :
    ∀ (i : Fin ((L ++ [U ++ V] ++ R).get (tripleIndex L [U ++ V] R tag)).length) t,
      t ∈ Icc (0 : ℝ) 1 →
      ∃ y : FaceDisks (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R),
        ∃ j : Fin ((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get y.1).length,
          faceCutFullMap L R U V d C y = (tripleIndex L [U ++ V] R tag,
            wordPoint ((L ++ [U ++ V] ++ R).get (tripleIndex L [U ++ V] R tag)) i t) ∧
          (((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get y.1).get j).1 =
            (((L ++ [U ++ V] ++ R).get (tripleIndex L [U ++ V] R tag)).get i).1 ∧
          y.2 = wordPoint ((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get y.1) j t := by
  let Q := L ++ [U ++ [(d, true)], (d, false) :: V] ++ R
  let e := tripleIndex L [U ++ [(d, true)], (d, false) :: V] R
  rcases tag with (k | k) | k
  · rw [tripleIndex_word]
    intro i t ht
    have hw : Q.get (e (.inl (.inl k))) = L.get k := tripleIndex_word _ _ _ _
    let j : Fin (Q.get (e (.inl (.inl k)))).length := finCongr (congrArg List.length hw).symm i
    refine ⟨(e (.inl (.inl k)), wordPoint _ j t), j, ?_, ?_, rfl⟩
    · rw [faceCutFullMap_apply]
      change (_, wordPoint _ j t) = (_, wordPoint _ i t)
      exact Prod.ext rfl (wordPoint_cast hw i t)
    · exact congrArg Prod.fst (wordGet_cast hw i)
  · have hk : k = 0 := Subsingleton.elim _ _
    subst k
    rw [tripleIndex_word]
    simp only [Sum.elim_inl, Sum.elim_inr, List.get_cons_zero]
    intro i t ht
    have hpar := dartParameter_mem ((U ++ V).get i) ht
    by_cases hiU : i.val < U.length
    · let idx : Fin Q.length := e (.inl (.inr ⟨0, by simp⟩))
      have hw : Q.get idx = U ++ [(d, true)] := by
        change (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get (e _) = _
        rw [tripleIndex_word]
        rfl
      let j : Fin (Q.get idx).length := ⟨i.val, by rw [hw]; simp; omega⟩
      have hget : (Q.get idx).get j = (U ++ V).get i := by
        rw [List.get_of_eq hw]
        simp only [List.get_eq_getElem, j]
        exact (List.getElem_append_left hiU).trans (List.getElem_append_left hiU).symm
      refine ⟨(idx, wordPoint _ j t), j, ?_, congrArg Prod.fst hget, rfl⟩
      have hz : wordPoint (Q.get idx) j t =
          diskAngle ((i.val + dartParameter ((U ++ V).get i) t) / (U.length + 1)) := by
        apply Subtype.ext
        simp only [wordPoint, diskAngle, hget, j, hw, List.length_append,
          List.length_cons, List.length_nil, Nat.cast_add, Nat.cast_one,
          zero_add, mul_div_assoc]
      rw [hz]
      change faceCutFullMap _ _ _ _ _ _ (e _, _) = _
      rw [faceCutFullMap_apply]
      change (_, faceCutMap C (.inl _)) = _
      apply Prod.ext (by rfl)
      have hr : (i.val : ℝ) + dartParameter ((U ++ V).get i) t ∈ Icc (0 : ℝ) U.length := by
        refine ⟨add_nonneg (Nat.cast_nonneg _) hpar.1, ?_⟩
        have : (i.val : ℝ) + 1 ≤ U.length := by exact_mod_cast hiU
        linarith [hpar.2]
      rw [faceCutMap_left_side C hr]
      apply Subtype.ext
      simp only [diskAngle, wordPoint, List.length_append, Nat.cast_add, mul_div_assoc]
    · have hiV : i.val - U.length < V.length := by
        have := i.isLt
        simp only [List.length_append] at this
        omega
      let idx : Fin Q.length := e (.inl (.inr ⟨1, by simp⟩))
      have hw : Q.get idx = (d, false) :: V := by
        change (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get (e _) = _
        rw [tripleIndex_word]
        rfl
      let j : Fin (Q.get idx).length := ⟨1 + (i.val - U.length), by rw [hw]; simp; omega⟩
      have hget : (Q.get idx).get j = (U ++ V).get i := by
        rw [List.get_of_eq hw]
        simp only [List.get_eq_getElem, j]
        rw [List.getElem_cons, dite_eq_right (by omega), List.getElem_append_right (by omega)]
        simp
      refine ⟨(idx, wordPoint _ j t), j, ?_, congrArg Prod.fst hget, rfl⟩
      have hz : wordPoint (Q.get idx) j t =
          diskAngle ((1 + (((i.val - U.length : ℕ) : ℝ) +
            dartParameter ((U ++ V).get i) t)) / (V.length + 1)) := by
        apply Subtype.ext
        simp only [wordPoint, diskAngle, hget, j, hw, List.length_cons,
          Nat.cast_add, Nat.cast_one]
        congr 2
        ring
      rw [hz]
      change faceCutFullMap _ _ _ _ _ _ (e _, _) = _
      rw [faceCutFullMap_apply]
      change (_, faceCutMap C (.inr _)) = _
      apply Prod.ext (by rfl)
      have hr : ((i.val - U.length : ℕ) : ℝ) + dartParameter ((U ++ V).get i) t ∈
          Icc (0 : ℝ) V.length := by
        refine ⟨add_nonneg (Nat.cast_nonneg _) hpar.1, ?_⟩
        have : ((i.val - U.length : ℕ) : ℝ) + 1 ≤ V.length := by exact_mod_cast hiV
        linarith [hpar.2]
      rw [faceCutMap_right_side C hr]
      apply Subtype.ext
      simp only [diskAngle, wordPoint, List.length_append, Nat.cast_add]
      congr 2
      have hiR : (i.val : ℝ) = U.length + ((i.val - U.length : ℕ) : ℝ) := by
        exact_mod_cast (show i.val = U.length + (i.val - U.length) by omega)
      rw [hiR]
      ring
  · rw [tripleIndex_word]
    intro i t ht
    have hw : Q.get (e (.inr k)) = R.get k := tripleIndex_word _ _ _ _
    let j : Fin (Q.get (e (.inr k))).length := finCongr (congrArg List.length hw).symm i
    refine ⟨(e (.inr k), wordPoint _ j t), j, ?_, ?_, rfl⟩
    · rw [faceCutFullMap_apply]
      change (_, wordPoint _ j t) = (_, wordPoint _ i t)
      exact Prod.ext rfl (wordPoint_cast hw i t)
    · exact congrArg Prod.fst (wordGet_cast hw i)

/-- A proper face subdivision is realized by two parameterized triangular
pieces of a square. Source: Gallier–Xu Definition 6.3(P2), p.84, and the
prescribed-boundary extension in Proposition 3.2, p.31 and Note F.4, p.167.
The old face is charted on the square; the two new faces are charted on its
diagonal triangles. Their fibers are exactly the fresh diagonal pairs.
The compact quotient map then identifies the generated edge relations, while
every old side retains its original interval parameter. -/
theorem face_subdivision_realized (L R : Presentation) (U V : Word) (d : ℕ)
    (hU : U ≠ []) (hV : V ≠ []) (hd : d ∉ labels (L ++ [U ++ V] ++ R)) :
    ∃ H : Realization (L ++ [U ++ V] ++ R) ≃ₜ
      Realization (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R),
      RespectsParameters (.face L R U V d hU hV hd) H := by
  obtain ⟨C⟩ := faceCutCharts_exists U.length V.length
    (List.length_pos_iff.mpr hU) (List.length_pos_iff.mpr hV)
  let q := faceCutFullMap L R U V d C
  have hsurvive : ∀ y (j : Fin ((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get y.1).length) s,
      s ∈ Icc (0 : ℝ) 1 →
      (((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get y.1).get j).1 ≠ d →
      (y.2 : ℂ) = sidePoint (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R) y.1 j s →
      ∃ i : Fin ((L ++ [U ++ V] ++ R).get (q y).1).length,
        (((L ++ [U ++ V] ++ R).get (q y).1).get i).1 =
          (((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get y.1).get j).1 ∧
        ((q y).2 : ℂ) = sidePoint (L ++ [U ++ V] ++ R) (q y).1 i s := by
    rintro ⟨k, z⟩ j s hs hj hz
    obtain ⟨tag, rfl⟩ := (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R).surjective k
    dsimp only [Prod.fst, Prod.snd] at *
    change Fin ((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get
      (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R tag)).length at j
    have hz' : z = wordPoint ((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get
      (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R tag)) j s := Subtype.ext hz
    subst z
    obtain ⟨i, hi, hq⟩ := faceCutFullMap_survives L R U V d C tag j s hs hj
    dsimp only [q]
    rw [hq]
    exact ⟨i, hi, rfl⟩
  have hseam : ∀ x y (i : Fin ((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get x.1).length)
      (j : Fin ((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get y.1).length) s,
      s ∈ Icc (0 : ℝ) 1 →
      (((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get x.1).get i).1 = d →
      (((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get y.1).get j).1 = d →
      (x.2 : ℂ) = sidePoint (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R) x.1 i s →
      (y.2 : ℂ) = sidePoint (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R) y.1 j s → q x = q y := by
    rintro ⟨k, z⟩ ⟨l, w⟩ i j s hs hi hj hz hw
    obtain ⟨tag, rfl⟩ := (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R).surjective k
    obtain ⟨tag', rfl⟩ := (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R).surjective l
    dsimp only [Prod.fst, Prod.snd] at *
    change Fin ((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get
      (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R tag)).length at i
    change Fin ((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get
      (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R tag')).length at j
    have hz' : z = wordPoint ((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get
      (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R tag)) i s := Subtype.ext hz
    have hw' : w = wordPoint ((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get
      (tripleIndex L [U ++ [(d, true)], (d, false) :: V] R tag')) j s := Subtype.ext hw
    subst z w
    have hc : q (lowerSeamPoint L R U V d s) = q (upperSeamPoint L R U V d s) := by
      dsimp only [q, lowerSeamPoint, upperSeamPoint]
      rw [faceCutFullMap_apply, faceCutFullMap_apply]
      change (_, faceCutMap C (.inl _)) = (_, faceCutMap C (.inr _))
      exact Prod.ext rfl (faceCutMap_seam C hs)
    rcases faceCutFull_seam_point L R U V d hd tag i s hi with h | h <;>
      rcases faceCutFull_seam_point L R U V d hd tag' j s hj with h' | h'
    · rw [h, h']
    · rw [h, h']; exact hc
    · rw [h, h']; exact hc.symm
    · rw [h, h']
  have hlift : ∀ x (i : Fin ((L ++ [U ++ V] ++ R).get x.1).length) t,
      t ∈ Icc (0 : ℝ) 1 → (x.2 : ℂ) = sidePoint (L ++ [U ++ V] ++ R) x.1 i t →
      ∃ y : FaceDisks (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R),
        ∃ j : Fin ((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get y.1).length,
          q y = x ∧
          (((L ++ [U ++ [(d, true)], (d, false) :: V] ++ R).get y.1).get j).1 =
            (((L ++ [U ++ V] ++ R).get x.1).get i).1 ∧
          (y.2 : ℂ) = sidePoint (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R) y.1 j t := by
    rintro ⟨k, z⟩ i t ht hz
    obtain ⟨tag, rfl⟩ := (tripleIndex L [U ++ V] R).surjective k
    dsimp only [Prod.fst, Prod.snd] at *
    change Fin ((L ++ [U ++ V] ++ R).get (tripleIndex L [U ++ V] R tag)).length at i
    have hz' : z = wordPoint ((L ++ [U ++ V] ++ R).get (tripleIndex L [U ++ V] R tag)) i t := Subtype.ext hz
    subst z
    obtain ⟨y, j, hq, hj, hy⟩ := faceCutFullMap_lift L R U V d C tag i t ht
    exact ⟨y, j, hq, hj, congrArg Subtype.val hy⟩
  obtain ⟨H, hH⟩ := presentation_surgery d hd q (faceCutFullMap_quotient L R U V d C)
    hsurvive hseam (faceCutFullMap_fiber L R U V d C) hlift
  refine ⟨H, ?_⟩
  intro x y i j t s ht hs hp hx hy
  change _ = _ ∧ t = s at hp
  rcases hp with ⟨he, rfl⟩
  exact hH x y i j t ht he hx hy

private theorem rename_rotated_realized {P Q : Presentation} (e : ℕ ≃ ℕ) (flip : ℕ → Bool)
    (f : Fin P.length ≃ Fin Q.length)
    (h : ∀ i, List.IsRotated
      ((P.get i).map fun a ↦ (e a.1, if flip a.1 then !a.2 else a.2)) (Q.get (f i))) :
    ∃ H : Realization P ≃ₜ Realization Q, RespectsParameters (.rename e flip f h) H := by
  let rename : Dart → Dart := fun a ↦ (e a.1, if flip a.1 then !a.2 else a.2)
  let S : Presentation := P.map (List.map rename)
  let f₀ : Fin P.length ≃ Fin S.length := finCongr (List.length_map ..).symm
  have hw (i : Fin P.length) : (P.get i).map rename = S.get (f₀ i) := by
    simp only [S, f₀, List.get_eq_getElem, List.getElem_map, finCongr_apply, Fin.val_cast]
  obtain ⟨E, hE, _⟩ := labelRenaming_realized e flip f₀ hw
  have hR : Reindexed S Q := by
    refine ⟨f₀.symm.trans f, ?_⟩
    intro i
    obtain ⟨i, rfl⟩ := f₀.surjective i
    simpa only [Equiv.trans_apply, Equiv.symm_apply_apply, ← hw] using h i
  obtain ⟨R, hR⟩ := reindex_realized hR
  refine ⟨E.trans R, ?_⟩
  intro x y i j t s ht hs hp hx hy
  have hlen : (P.get x.1).length = (S.get (f₀ x.1)).length := by
    rw [← hw, List.length_map]
  let k := finCongr hlen i
  have hk : ((S.get (f₀ x.1)).get k).1 = e ((P.get x.1).get i).1 := by
    rw [List.get_of_eq (hw x.1).symm]
    simp [k, rename, List.get_eq_getElem]
  let z : FaceDisks S := (f₀ x.1, wordPoint _ k s)
  have hz : (z.2 : ℂ) = sidePoint S z.1 k s := rfl
  have hEz : E (project P x) = project S z := by
    apply hE x z i k t s ht hs
    · change e ((P.get x.1).get i).1 = ((S.get (f₀ x.1)).get k).1 ∧
        s = if flip ((P.get x.1).get i).1 then 1 - t else t
      exact ⟨hk.symm, hp.2⟩
    · exact hx
    · exact hz
  change R (E (project P x)) = _
  rw [hEz]
  apply hR z y k j s s hs hs
  · change ((S.get (f₀ x.1)).get k).1 = ((Q.get y.1).get j).1 ∧ s = s
    exact ⟨hk.trans hp.1, rfl⟩
  · exact hz
  · exact hy

/-- Every elementary presentation move has its prescribed-parameter geometric
realization. Source: Gallier–Xu Definition 6.3, pp.84–86; Proposition 3.2,
p.31; Note F.4, p.167. Use the explicit P1/P2 disk maps, rotate cyclic starts,
rename labeled intervals, and take inverse homeomorphisms for inverse moves. -/
theorem elementary_realized {P Q : Presentation} (h : Elementary P Q) :
    ∃ H : Realization P ≃ₜ Realization Q, RespectsParameters h H := by
  induction h with
  | edge P a b c ha hb hc hbc => exact edge_subdivision_realized P a b c ha hb hc hbc
  | face L R U V d hU hV hd => exact face_subdivision_realized L R U V d hU hV hd
  | inverse h ih =>
    obtain ⟨H, hH⟩ := ih
    exact ⟨H.symm, hH.symm⟩
  | reindex h => exact reindex_realized h
  | rename e flip f h => exact rename_rotated_realized e flip f h

/-- Equivalence by a finite sequence of actual realized source moves. -/
def PresentationEquivalent (P Q : Presentation) : Prop := Nonempty (RealizedSequence P Q)

private theorem PresentationEquivalent.refl (P : Presentation) : PresentationEquivalent P P :=
  ⟨.nil P⟩

private theorem PresentationEquivalent.trans {P Q R : Presentation}
    (h : PresentationEquivalent P Q) (h' : PresentationEquivalent Q R) :
    PresentationEquivalent P R := by
  obtain ⟨s⟩ := h
  obtain ⟨t⟩ := h'
  exact ⟨s.trans t⟩

private theorem PresentationEquivalent.symm {P Q : Presentation}
    (h : PresentationEquivalent P Q) : PresentationEquivalent Q P := by
  obtain ⟨s⟩ := h
  exact ⟨s.reverse⟩

private theorem Elementary.equivalent {P Q : Presentation} (h : Elementary P Q) :
    PresentationEquivalent P Q := by
  obtain ⟨H, hH⟩ := elementary_realized h
  exact ⟨.cons h H hH (.nil Q)⟩

private theorem reindexed_singleton {U V : Word} (h : List.IsRotated U V) :
    Reindexed [U] [V] := by
  refine ⟨Equiv.refl _, ?_⟩
  intro i
  fin_cases i
  exact h

private theorem reindexed_pair {U V U' V' : Word}
    (hU : List.IsRotated U U') (hV : List.IsRotated V V') :
    Reindexed [U, V] [U', V'] := by
  refine ⟨Equiv.refl _, ?_⟩
  intro i
  fin_cases i
  · exact hU
  · exact hV

/-- Gallier–Xu's handle-extraction interchange rule, Lemma 6.1 Step 4,
p.94: cut at the end of the first substring, cyclically reindex both donor
faces, merge along the old paired edge, and rotate the resulting face.
The two proper cuts retain every displayed substring, including empty ones. -/
theorem paired_edge_interchange (a c : ℕ) (U V X : Word)
    (ha : a ∉ labels [U, V, X])
    (hc : c ∉ labels [(a, true) :: (U ++ V ++ (a, false) :: X)]) :
    PresentationEquivalent [(a, true) :: (U ++ V ++ (a, false) :: X)]
      [(c, false) :: (V ++ U ++ (c, true) :: X)] := by
  have hac : a ≠ c := by
    intro h
    apply hc
    simp [← h, labels, occurrences]
  have hcut := (Elementary.face [] [] ((a, true) :: U) (V ++ (a, false) :: X) c
    (by simp) (by simp) (by simpa [List.append_assoc] using hc)).equivalent
  have hreindex : PresentationEquivalent
      [((a, true) :: U) ++ [(c, true)], (c, false) :: (V ++ (a, false) :: X)]
      [U ++ [(c, true), (a, true)], (a, false) :: (X ++ (c, false) :: V)] := by
    apply Elementary.equivalent
    apply Elementary.reindex
    apply reindexed_pair
    · simpa [List.append_assoc] using
        (List.IsRotated.cons_append_singleton (a := (a, true)) (l := U ++ [(c, true)]))
    · simpa [List.append_assoc] using
        (List.isRotated_append (l := (c, false) :: V) (l' := (a, false) :: X))
  have hmerge := (Elementary.face [] [] (U ++ [(c, true)]) (X ++ (c, false) :: V) a
    (by simp) (by simp) (by
      simpa [labels, occurrences, List.mem_map, List.mem_flatten, List.mem_append,
        hac, and_comm, and_left_comm, and_assoc] using ha)).inverse.equivalent
  have hrotate : PresentationEquivalent
      [(U ++ [(c, true)]) ++ (X ++ (c, false) :: V)]
      [(c, false) :: (V ++ U ++ (c, true) :: X)] := by
    apply Elementary.equivalent
    apply Elementary.reindex
    apply reindexed_singleton
    simpa [List.append_assoc] using
      (List.isRotated_append (l := U ++ (c, true) :: X) (l' := (c, false) :: V))
  apply PresentationEquivalent.trans (Q :=
    [((a, true) :: U) ++ [(c, true)], (c, false) :: (V ++ (a, false) :: X)])
  · simpa [List.append_assoc] using hcut
  apply hreindex.trans
  apply PresentationEquivalent.trans (Q := [(U ++ [(c, true)]) ++ (X ++ (c, false) :: V)])
  · simpa [List.append_assoc] using hmerge
  exact hrotate

private theorem splitWord_unchanged (a b c : ℕ) (w : Word)
    (h : ∀ d ∈ w, d.1 ≠ a) : w.flatMap (splitDart a b c) = w := by
  induction w with
  | nil => rfl
  | cons d w ih =>
    rw [List.flatMap_cons]
    have hd := h d (by simp)
    simp only [splitDart, ite_eq_right hd, List.singleton_append]
    rw [ih (fun e he ↦ h e (by simp [he]))]

/-- Proper cancellation of a spur with nonempty surviving words on both sides.
Source: Seifert–Threlfall §38 Step 2, p.140; Gallier–Xu Definition 6.3,
p.84. Cut between the two spur sides, undo the subdivision formed by one
spur side and the fresh cut side, and merge the two proper donor faces.
All three operations are genuine P1/P2 moves with fresh labels. -/
theorem proper_spur_cancellation (a : ℕ) (R S : Word) (hR : R ≠ []) (hS : S ≠ [])
    (ha : a ∉ labels [R, S]) :
    PresentationEquivalent [R ++ (a, true) :: (a, false) :: S] [R ++ S] := by
  obtain ⟨c, hc⟩ := (insert a (labels [R, S])).exists_notMem
  obtain ⟨d, hd⟩ := (insert a (insert c (labels [R, S]))).exists_notMem
  simp only [Finset.mem_insert, not_or] at hc hd
  have hRc : ∀ e ∈ R, e.1 ≠ c := fun e he ↦ fresh_dart [R, S] hc.2 (by simp) he
  have hSc : ∀ e ∈ S, e.1 ≠ c := fun e he ↦ fresh_dart [R, S] hc.2 (by simp) he
  have hsub : subdivideEdge [R ++ [(c, true)], (c, false) :: S] c a d =
      [R ++ [(a, true), (d, true)], (d, false) :: (a, false) :: S] := by
    change [((R ++ [(c, true)]).flatMap (splitDart c a d)),
      (((c, false) :: S).flatMap (splitDart c a d))] = _
    rw [List.flatMap_append, splitWord_unchanged c a d R hRc]
    simp only [List.flatMap_cons, List.flatMap_nil, splitDart,
      Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append, List.nil_append]
    rw [splitWord_unchanged c a d S hSc]
  have hcut := (Elementary.face [] [] (R ++ [(a, true)]) ((a, false) :: S) d
    (by simp) (by simp) (by
      simpa [labels, occurrences, List.mem_map, List.mem_flatten, List.mem_append,
        hd.1, and_comm, and_left_comm, and_assoc] using hd.2.2)).equivalent
  have hcontract : PresentationEquivalent
      [R ++ [(a, true), (d, true)], (d, false) :: (a, false) :: S]
      [R ++ [(c, true)], (c, false) :: S] := by
    rw [← hsub]
    apply Elementary.equivalent
    apply Elementary.inverse
    apply Elementary.edge
    · simp [labels, occurrences]
    · simpa [labels, occurrences, List.mem_map, List.mem_flatten, List.mem_append,
        Ne.symm hc.1, and_comm, and_left_comm, and_assoc] using ha
    · simpa [labels, occurrences, List.mem_map, List.mem_flatten, List.mem_append,
        hd.2.1, and_comm, and_left_comm, and_assoc] using hd.2.2
    · exact Ne.symm hd.1
  have hmerge := (Elementary.face [] [] R S c hR hS (by
    simpa [labels, occurrences, List.mem_map, List.mem_flatten, List.mem_append,
      and_comm, and_left_comm, and_assoc] using hc.2)).inverse.equivalent
  apply PresentationEquivalent.trans (Q :=
    [R ++ [(a, true), (d, true)], (d, false) :: (a, false) :: S])
  · simpa [List.append_assoc] using hcut
  apply hcontract.trans
  simpa using hmerge

private theorem singleton_rotation {U V : Word} (h : List.IsRotated U V) :
    PresentationEquivalent [U] [V] := (Elementary.reindex (reindexed_singleton h)).equivalent

/-- A spur with exactly one surviving positive side is removed by subdividing
that side once, applying proper cancellation, and undoing the subdivision.
Source: Seifert–Threlfall §37–§38, pp.138–140, and Gallier–Xu P1, p.84.
The surviving side is split globally at one half and reassembled only after
the temporary diagonal has been removed. -/
theorem one_side_spur_cancellation (a h : ℕ) (hah : a ≠ h) :
    PresentationEquivalent [[(a, true), (a, false), (h, true)]] [[(h, true)]] := by
  obtain ⟨b, hb⟩ := (insert a ({h} : Finset ℕ)).exists_notMem
  obtain ⟨c, hc⟩ := (insert b (insert a ({h} : Finset ℕ))).exists_notMem
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb hc
  have hsplit := (Elementary.edge [[(a, true), (a, false), (h, true)]] h b c
    (by simp [labels, occurrences]) (by simp [labels, occurrences, hb.1, hb.2])
    (by simp [labels, occurrences, hc.2.1, hc.2.2]) (Ne.symm hc.1)).equivalent
  have hrot : PresentationEquivalent [[(a, true), (a, false), (b, true), (c, true)]]
      [[(c, true), (a, true), (a, false), (b, true)]] := by
    apply singleton_rotation
    exact List.isRotated_append (l := [(a, true), (a, false), (b, true)]) (l' := [(c, true)])
  have hcancel := proper_spur_cancellation a [(c, true)] [(b, true)]
    (by simp) (by simp) (by simp [labels, occurrences, Ne.symm hc.2.1, Ne.symm hb.1])
  have hrot' : PresentationEquivalent [[(c, true), (b, true)]] [[(b, true), (c, true)]] :=
    singleton_rotation (List.isRotated_append (l := [(c, true)]) (l' := [(b, true)]))
  have hundo := (Elementary.edge [[(h, true)]] h b c
    (by simp [labels, occurrences]) (by simp [labels, occurrences, hb.2])
    (by simp [labels, occurrences, hc.2.2]) (Ne.symm hc.1)).inverse.equivalent
  apply PresentationEquivalent.trans (Q := [[(a, true), (a, false), (b, true), (c, true)]])
  · simpa [subdivideEdge, hah] using hsplit
  apply hrot.trans
  apply PresentationEquivalent.trans hcancel
  apply hrot'.trans
  simpa [subdivideEdge] using hundo

private theorem rename_equivalent (P : Presentation) (e : ℕ ≃ ℕ) (flip : ℕ → Bool) :
    PresentationEquivalent P (P.map (List.map (fun a ↦ (e a.1, if flip a.1 then !a.2 else a.2)))) := by
  apply Elementary.equivalent
  apply Elementary.rename e flip (finCongr (List.length_map ..).symm)
  intro i
  have he : ((P.get i).map fun a ↦ (e a.1, if flip a.1 then !a.2 else a.2)) =
      (P.map (List.map (fun a ↦ (e a.1, if flip a.1 then !a.2 else a.2)))).get
        ((finCongr (List.length_map ..).symm) i) := by simp [List.get_eq_getElem]
  rw [he]

private theorem one_dart_spur_cancellation (a : ℕ) (h : Dart) (hah : a ≠ h.1) :
    PresentationEquivalent [[(a, true), (a, false), h]] [[h]] := by
  rcases h with ⟨h, b⟩
  cases b
  · have he := rename_equivalent [[(a, true), (a, false), (h, false)]] (Equiv.refl ℕ)
      (fun k ↦ decide (k = h))
    have he' := rename_equivalent [[(h, false)]] (Equiv.refl ℕ) (fun k ↦ decide (k = h))
    have hs := one_side_spur_cancellation a h hah
    apply PresentationEquivalent.trans (Q := [[(a, true), (a, false), (h, true)]])
    · simpa [hah] using he
    apply hs.trans
    simpa using he'.symm
  · exact one_side_spur_cancellation a h hah

/-- The nonempty-residual spur cancellation used in the polygon reduction.
Source: Gallier–Xu Lemma 6.1 Step 1, p.92, realized by the proper
Seifert–Threlfall cancellation of §38, p.140. Split a residual of length
at least two into two nonempty strings and rotate them around the spur.
For length one, subdivide the remaining side once, perform proper
cancellation, and undo that subdivision. Thus no whole-circle face merge
or empty polygon is used. -/
theorem spur_cancellation (a : ℕ) (X : Word) (hX : X ≠ []) (ha : a ∉ labels [X]) :
    PresentationEquivalent [(a, true) :: (a, false) :: X] [X] := by
  cases X with
  | nil => exact False.elim (hX rfl)
  | cons x X =>
    cases X with
    | nil =>
      apply one_dart_spur_cancellation
      intro h
      apply ha
      simp [labels, occurrences, h]
    | cons y Y =>
      have hrot : PresentationEquivalent [(a, true) :: (a, false) :: x :: y :: Y]
          [(y :: Y) ++ [(a, true), (a, false), x]] := by
        apply singleton_rotation
        exact List.isRotated_append (l := [(a, true), (a, false), x]) (l' := y :: Y)
      have hcancel := proper_spur_cancellation a (y :: Y) [x] (by simp) (by simp) (by
        simpa [labels, occurrences, List.mem_map, List.mem_flatten, List.mem_append,
          and_comm, and_left_comm, and_assoc] using ha)
      apply hrot.trans
      apply PresentationEquivalent.trans hcancel
      apply singleton_rotation
      exact List.isRotated_append (l := y :: Y) (l' := [x])

/-- Either orientation of the cancellable paired side has the same proper
finite cancellation. Reverse that label's chosen interval orientation,
apply the positive-side cancellation, and observe that the residual has no
occurrence of the label. -/
theorem signed_spur_cancellation (a : Dart) (X : Word) (hX : X ≠ [])
    (ha : a.1 ∉ labels [X]) : PresentationEquivalent [a :: inverse a :: X] [X] := by
  rcases a with ⟨a, b⟩
  cases b
  · let flip : ℕ → Bool := fun k ↦ decide (k = a)
    have hmap : X.map (fun d ↦ ((Equiv.refl ℕ) d.1, if flip d.1 then !d.2 else d.2)) = X := by
      conv_rhs => rw [← List.map_id X]
      apply List.map_congr_left
      intro d hd
      have hne := fresh_dart [X] ha (by simp) hd
      simp [flip, hne]
    have he := rename_equivalent [[(a, false), (a, true)] ++ X] (Equiv.refl ℕ) flip
    apply PresentationEquivalent.trans (Q := [(a, true) :: (a, false) :: X])
    · simp only [List.map_cons, List.map_nil, List.map_append] at he
      rw [hmap] at he
      simpa [inverse, flip] using he
    exact spur_cancellation a X hX ha
  · exact spur_cancellation a X hX ha

private theorem Oriented.count_le_one {P : Presentation} (h : Oriented P) (d : Dart) :
    (occurrences P).count d ≤ 1 := by
  by_cases hd : d ∈ occurrences P
  · have hl : d.1 ∈ labels P := by
      simp only [labels, List.mem_toFinset, List.mem_map]
      exact ⟨d, hd, rfl⟩
    rcases d with ⟨a, b⟩
    rcases h.2 a hl with h | h | h <;> cases b <;> simp_all
  · rw [List.count_eq_zero_of_not_mem hd]
    omega

private theorem Oriented.paired_fresh {a : ℕ} {U V X : Word}
    (h : Oriented [(a, true) :: (U ++ (a, false) :: (V ++ X))]) :
    a ∉ labels [U, V, X] := by
  have hp := h.count_le_one (a, true)
  have hn := h.count_le_one (a, false)
  simp [occurrences, List.count_append] at hp hn
  simp only [labels, occurrences, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.mem_toFinset, List.mem_map, List.mem_append, not_exists, not_and]
  intro d hd hda
  rcases d with ⟨a', b⟩
  dsimp only [Prod.fst] at hda
  subst a'
  rcases hd with hd | hd | hd <;> cases b
  all_goals have := List.count_pos_iff.mpr hd
  all_goals omega

private theorem Oriented.spur_fresh {a : ℕ} {X : Word}
    (h : Oriented [(a, true) :: (a, false) :: X]) : a ∉ labels [X] := by
  have hf := Oriented.paired_fresh (a := a) (U := []) (V := X) (X := []) (by simpa using h)
  simpa [labels, occurrences] using hf

/-- Extraction of an interleaved pair as a handle by three proper
interchanges. Source: Gallier–Xu Lemma 6.1 Step 4, pp.94–95. The first
interchange moves `U` behind `V`; the second moves the opposite `b` side
next to the first new edge; the third makes the four handle sides
consecutive. Cyclic rotations give the residual order `Y X V U`. -/
theorem interleaved_handle_extraction (a b : ℕ) (U V X Y : Word)
    (ha : a ∉ labels [U, V, X, Y]) (hb : b ∉ labels [U, V, X, Y]) (hab : a ≠ b) :
    ∃ e d : ℕ, e ≠ d ∧ e ∉ labels [U, V, X, Y] ∧ d ∉ labels [U, V, X, Y] ∧
      PresentationEquivalent
        [(a, true) :: (U ++ (b, true) :: (V ++ (a, false) :: (X ++ (b, false) :: Y)))]
        [(e, true) :: (d, false) :: (e, false) :: (d, true) :: (Y ++ X ++ V ++ U)] := by
  obtain ⟨c, hc⟩ := (insert a (insert b (labels [U, V, X, Y]))).exists_notMem
  obtain ⟨d, hd⟩ := (insert c (insert a (insert b (labels [U, V, X, Y])))).exists_notMem
  obtain ⟨e, he⟩ := (insert d (insert c (insert a (insert b (labels [U, V, X, Y]))))).exists_notMem
  simp only [Finset.mem_insert, not_or] at hc hd he
  have h1 := paired_edge_interchange a c U ((b, true) :: V) (X ++ (b, false) :: Y)
    (by simpa [labels, occurrences, List.mem_map, List.mem_flatten, List.mem_append,
      hab, and_comm, and_left_comm, and_assoc] using ha)
    (by simpa [labels, occurrences, List.mem_map, List.mem_flatten, List.mem_append,
      hc.1, hc.2.1, and_comm, and_left_comm, and_assoc] using hc.2.2)
  have h2 := paired_edge_interchange b d (V ++ U) ((c, true) :: X) (Y ++ [(c, false)])
    (by simpa [labels, occurrences, List.mem_map, List.mem_flatten, List.mem_append,
      Ne.symm hc.2.1, and_comm, and_left_comm, and_assoc] using hb)
    (by simpa [labels, occurrences, List.mem_map, List.mem_flatten, List.mem_append,
      hd.1, hd.2.2.1, and_comm, and_left_comm, and_assoc] using hd.2.2.2)
  have h3 := paired_edge_interchange c e (X ++ V ++ U) ((d, true) :: Y) [(d, false)]
    (by simpa [labels, occurrences, List.mem_map, List.mem_flatten, List.mem_append,
      Ne.symm hd.1, and_comm, and_left_comm, and_assoc] using hc.2.2)
    (by simpa [labels, occurrences, List.mem_map, List.mem_flatten, List.mem_append,
      he.1, he.2.1, and_comm, and_left_comm, and_assoc] using he.2.2.2.2)
  refine ⟨e, d, he.1, he.2.2.2.2, hd.2.2.2, ?_⟩
  have r1 : PresentationEquivalent
      [(c, false) :: ((b, true) :: V ++ U ++ (c, true) :: (X ++ (b, false) :: Y))]
      [(b, true) :: ((V ++ U) ++ (c, true) :: X ++ (b, false) :: (Y ++ [(c, false)]))] := by
    apply singleton_rotation
    simpa [List.append_assoc] using (List.IsRotated.cons_append_singleton
      (a := (c, false)) (l := (b, true) :: (V ++ U ++ (c, true) :: (X ++ (b, false) :: Y))))
  have r2 : PresentationEquivalent
      [(d, false) :: ((c, true) :: X ++ (V ++ U) ++ (d, true) :: (Y ++ [(c, false)]))]
      [(c, true) :: ((X ++ V ++ U) ++ (d, true) :: Y ++ (c, false) :: [(d, false)])] := by
    apply singleton_rotation
    simpa [List.append_assoc] using (List.IsRotated.cons_append_singleton
      (a := (d, false)) (l := (c, true) :: (X ++ V ++ U ++ (d, true) :: (Y ++ [(c, false)]))))
  have r3 : PresentationEquivalent
      [(e, false) :: ((d, true) :: Y ++ (X ++ V ++ U) ++ (e, true) :: [(d, false)])]
      [(e, true) :: (d, false) :: (e, false) :: (d, true) :: (Y ++ X ++ V ++ U)] := by
    apply singleton_rotation
    simpa [List.append_assoc] using
      (List.isRotated_append (l := (e, false) :: (d, true) :: (Y ++ X ++ V ++ U))
        (l' := [(e, true), (d, false)]))
  apply PresentationEquivalent.trans (Q :=
    [(c, false) :: ((b, true) :: V ++ U ++ (c, true) :: (X ++ (b, false) :: Y))])
  · simpa [List.append_assoc] using h1
  apply r1.trans
  apply PresentationEquivalent.trans (Q :=
    [(d, false) :: ((c, true) :: X ++ (V ++ U) ++ (d, true) :: (Y ++ [(c, false)]))])
  · simpa [List.append_assoc] using h2
  apply r2.trans
  apply PresentationEquivalent.trans (Q :=
    [(e, false) :: ((d, true) :: Y ++ (X ++ V ++ U) ++ (e, true) :: [(d, false)])])
  · simpa [List.append_assoc] using h3
  exact r3

private def facesShareLabel (P : Presentation) (i j : Fin P.length) : Prop :=
  ∃ a ∈ P.get i, ∃ b ∈ P.get j, a.1 = b.1

/-- Connectedness of the realized surface forces the face adjacency relation
to have one component. Source: Lee's classification proof, Step 1, p.173;
Gallier–Xu Lemma 6.1 Step 3, p.94. Map each parameter disk to its component
in the finite graph of shared labels. Every generator of the surface quotient
preserves this component. The induced continuous map has discrete target,
so connectedness makes it constant. -/
theorem face_adjacency_connected (P : Presentation) [PreconnectedSpace (Realization P)]
    (i j : Fin P.length) : Relation.EqvGen (facesShareLabel P) i j := by
  let r := Relation.EqvGen.setoid (facesShareLabel P)
  let components := Quotient r
  let : DiscreteTopology components := by
    apply discreteTopology_iff_isOpen_singleton.mpr
    intro x
    apply (isQuotientMap_quotient_mk' (s := r)).isOpen_preimage.mp
    exact isOpen_discrete _
  have hgen (x y : FaceDisks P) (h : edgeIdentification P x y) :
      (Quotient.mk r x.1 : components) = Quotient.mk r y.1 := by
    obtain ⟨a, b, t, ht, he, hx, hy⟩ := h
    apply Quotient.sound
    exact Relation.EqvGen.rel _ _ ⟨_, List.get_mem _ a, _, List.get_mem _ b, he⟩
  have hrel (x y : FaceDisks P) (h : Relation.EqvGen (edgeIdentification P) x y) :
      (Quotient.mk r x.1 : components) = Quotient.mk r y.1 := by
    induction h with
    | rel x y h => exact hgen x y h
    | refl x => rfl
    | symm x y h ih => exact ih.symm
    | trans x y z h h' ih ih' => exact ih.trans ih'
  let F : Realization P → components := Quotient.lift (fun x : FaceDisks P ↦ Quotient.mk r x.1) hrel
  have hF : Continuous F :=
    ((continuous_quotient_mk' (s := r)).comp continuous_fst).quotient_lift hrel
  have he := TotallyDisconnectedSpace.eq_of_continuous F hF
    (project P (i, ⟨0, by simp⟩)) (project P (j, ⟨0, by simp⟩))
  exact Quotient.exact he

private theorem Reindexed.refl (P : Presentation) : Reindexed P P :=
  ⟨Equiv.refl _, fun _ ↦ List.IsRotated.refl _⟩

private theorem Reindexed.trans {P Q R : Presentation} (h : Reindexed P Q) (h' : Reindexed Q R) :
    Reindexed P R := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := h'
  exact ⟨f.trans g, fun i ↦ (hf i).trans (hg (f i))⟩

private theorem Reindexed.cons {P Q : Presentation} (h : Reindexed P Q) (w : Word) :
    Reindexed (w :: P) (w :: Q) := by
  obtain ⟨f, hf⟩ := h
  let e := ((appendIndex [w] P).symm.trans (Equiv.sumCongr (Equiv.refl _) f)).trans
    (appendIndex [w] Q)
  refine ⟨e, ?_⟩
  intro i
  obtain ⟨i, rfl⟩ := (appendIndex [w] P).surjective i
  cases i with
  | inl i =>
    change List.IsRotated (([w] ++ P).get _) (([w] ++ Q).get _)
    simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.refl_apply]
    rw [appendIndex_left, appendIndex_left]
  | inr i =>
    change List.IsRotated (([w] ++ P).get _) (([w] ++ Q).get _)
    simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply, Sum.map_inr]
    rw [appendIndex_right, appendIndex_right]
    exact hf i

private theorem Reindexed.swap (u v : Word) (P : Presentation) :
    Reindexed (u :: v :: P) (v :: u :: P) := by
  refine ⟨Equiv.swap 0 1, ?_⟩
  rintro ⟨i, hi⟩
  cases i with
  | zero =>
    have he : (⟨0, hi⟩ : Fin (u :: v :: P).length) = 0 := rfl
    rw [he, Equiv.swap_apply_left]
    exact List.IsRotated.refl _
  | succ i =>
    cases i with
    | zero =>
      have he : (⟨1, hi⟩ : Fin (u :: v :: P).length) = 1 := rfl
      rw [he, Equiv.swap_apply_right]
      exact List.IsRotated.refl _
    | succ i =>
      rw [Equiv.swap_apply_of_ne_of_ne (by intro h; have := congrArg Fin.val h; simp at this)
        (by intro h; have := congrArg Fin.val h; simp at this)]
      change List.IsRotated (P.get ⟨i, by simpa using hi⟩) (P.get ⟨i, by simpa using hi⟩)
      exact List.IsRotated.refl _

private theorem reindexed_of_perm {P Q : Presentation} (h : P.Perm Q) : Reindexed P Q := by
  induction h with
  | nil => exact Reindexed.refl []
  | cons w h ih => exact ih.cons w
  | swap u v P => exact Reindexed.swap _ _ _
  | trans h h' ih ih' => exact ih.trans ih'

private theorem oriented_iff_nodup (P : Presentation) :
    Oriented P ↔ (∀ w ∈ P, w ≠ []) ∧ (occurrences P).Nodup := by
  constructor
  · intro h
    exact ⟨h.1, List.nodup_iff_count.mpr h.count_le_one⟩
  · rintro ⟨hne, hnd⟩
    refine ⟨hne, ?_⟩
    intro a ha
    have hp := List.nodup_iff_count.mp hnd (a, true)
    have hn := List.nodup_iff_count.mp hnd (a, false)
    have hm : 0 < (occurrences P).count (a, true) ∨ 0 < (occurrences P).count (a, false) := by
      simp only [labels, List.mem_toFinset, List.mem_map] at ha
      obtain ⟨⟨a', b⟩, hb, he⟩ := ha
      dsimp only [Prod.fst] at he
      subst a'
      cases b
      · exact Or.inr (List.count_pos_iff.mpr hb)
      · exact Or.inl (List.count_pos_iff.mpr hb)
    omega

private theorem Oriented.perm {P Q : Presentation} (h : Oriented P) (hp : P.Perm Q) :
    Oriented Q := by
  rw [oriented_iff_nodup] at h ⊢
  exact ⟨fun w hw ↦ h.1 w (hp.mem_iff.mpr hw), hp.flatten.nodup_iff.mp h.2⟩

private theorem Oriented.merge {U V : Word} {R : Presentation} {a : ℕ}
    (h : Oriented ((U ++ [(a, true)]) :: ((a, false) :: V) :: R))
    (hU : U ≠ []) : Oriented ((U ++ V) :: R) := by
  rw [oriented_iff_nodup] at h ⊢
  refine ⟨?_, ?_⟩
  · intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · simp [hU]
    · exact h.1 w (by simp [hw])
  · have hs : (occurrences ((U ++ V) :: R)).Sublist
        (occurrences ((U ++ [(a, true)]) :: ((a, false) :: V) :: R)) := by
      simp only [occurrences, List.flatten_cons, List.append_assoc, List.singleton_append]
      apply List.Sublist.append_left
      exact (List.Sublist.cons _ (List.Sublist.cons _ (List.Sublist.refl _)))
    exact h.2.sublist hs

private theorem Oriented.distinct_faces_disjoint {P : Presentation} (h : Oriented P)
    {i j : Fin P.length} (hij : i ≠ j) : List.Disjoint (P.get i) (P.get j) := by
  have hp := (List.nodup_flatten.mp (oriented_iff_nodup P |>.mp h).2).2
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact hp.rel_get_of_lt hij
  · exact (hp.rel_get_of_lt hij).symm

private theorem shared_distinct_faces (P : Presentation)
    [PreconnectedSpace (Realization P)] (hP : 2 ≤ P.length) :
    ∃ i j : Fin P.length, i ≠ j ∧ facesShareLabel P i j := by
  by_contra hn
  push Not at hn
  have hdiag : ∀ i j, facesShareLabel P i j → i = j := by
    intro i j h
    by_contra hij
    exact hn i j hij h
  have hclosure (i j : Fin P.length) (hc : Relation.EqvGen (facesShareLabel P) i j) : i = j := by
    induction hc with
    | rel i j h => exact hdiag i j h
    | refl i => rfl
    | symm i j h ih => exact ih.symm
    | trans i j k h h' ih ih' => exact ih.trans ih'
  have he := hclosure ⟨0, by omega⟩ ⟨1, by omega⟩
    (face_adjacency_connected P ⟨0, by omega⟩ ⟨1, by omega⟩)
  have := congrArg Fin.val he
  simp only [] at this
  omega

private theorem perm_two_to_front {P : Presentation} {u v : Word}
    (hu : u ∈ P) (hv : v ∈ P) (hne : u ≠ v) :
    ∃ R, P.Perm (u :: v :: R) := by
  refine ⟨(P.erase u).erase v, (List.perm_cons_erase hu).trans ?_⟩
  exact (List.perm_cons_erase ((List.mem_erase_of_ne (Ne.symm hne)).mpr hv)).cons u

private theorem Reindexed.rotate_head {P : Presentation} {u v : Word}
    (h : List.IsRotated u v) : Reindexed (u :: P) (v :: P) := by
  refine ⟨Equiv.refl _, ?_⟩
  rintro ⟨i, hi⟩
  cases i with
  | zero => exact h
  | succ i => exact List.IsRotated.refl _

private theorem Reindexed.occurrences_perm {P Q : Presentation} (hr : Reindexed P Q) :
    (occurrences P).Perm (occurrences Q) := by
  obtain ⟨e, he⟩ := hr
  apply List.perm_iff_count.mpr
  intro a
  simp only [occurrences, List.count_flatten]
  rw [← Fin.sum_univ_fun_getElem, ← Fin.sum_univ_fun_getElem]
  exact Fintype.sum_equiv e _ _ (fun i ↦ (he i).perm.count_eq a)

private def UnpairedDart (P : Presentation) (d : Dart) : Prop :=
  d ∈ occurrences P ∧ inverse d ∉ occurrences P

private theorem Reindexed.unpaired {P Q : Presentation} (hr : Reindexed P Q) (d : Dart) :
    UnpairedDart P d ↔ UnpairedDart Q d := by
  simp only [UnpairedDart, hr.occurrences_perm.mem_iff]

private theorem unpaired_merge (a : ℕ) (U V : Word) (R : Presentation) (d : Dart)
    (h : UnpairedDart ((U ++ [(a, true)]) :: ((a, false) :: V) :: R) d) :
    UnpairedDart ((U ++ V) :: R) d := by
  have hne : d.1 ≠ a := by
    intro he
    rcases d with ⟨d, t⟩
    dsimp at he
    subst d
    cases t <;> apply h.2 <;> simp [occurrences, inverse]
  have hp : d ≠ (a, true) := fun he ↦ hne (congrArg Prod.fst he)
  have hn : d ≠ (a, false) := fun he ↦ hne (congrArg Prod.fst he)
  rcases h with ⟨hd, hdi⟩
  constructor
  · simp only [occurrences, List.flatten_cons, List.mem_append, List.mem_cons,
      List.not_mem_nil, hp, hn, false_or, or_false] at hd ⊢
    tauto
  · intro hm
    apply hdi
    simp only [occurrences, List.flatten_cons, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hm ⊢
    tauto

private theorem Oriented.reindexed {P Q : Presentation} (h : Oriented P)
    (hr : Reindexed P Q) : Oriented Q := by
  obtain ⟨e, he⟩ := hr
  rw [oriented_iff_nodup] at h ⊢
  have hf : P.flatten.Perm Q.flatten := by
    apply List.perm_iff_count.mpr
    intro a
    simp only [List.count_flatten]
    rw [← Fin.sum_univ_fun_getElem, ← Fin.sum_univ_fun_getElem]
    exact Fintype.sum_equiv e _ _ (fun i ↦ (he i).perm.count_eq a)
  refine ⟨?_, hf.nodup_iff.mp h.2⟩
  intro w hw
  obtain ⟨j, rfl⟩ := List.get_of_mem hw
  have hlen := (he (e.symm j)).perm.length_eq
  simp only [Equiv.apply_symm_apply] at hlen
  intro hz
  have hempty : P.get (e.symm j) = [] := List.length_eq_zero_iff.mp (by rw [hlen, hz]; rfl)
  exact h.1 _ (List.get_mem _ _) hempty

private theorem oriented_shared_faces {P : Presentation} (ho : Oriented P)
    [PreconnectedSpace (Realization P)] (hlen : 2 ≤ P.length) :
    ∃ u ∈ P, ∃ v ∈ P, ∃ a : ℕ,
      u ≠ v ∧ (a, true) ∈ u ∧ (a, false) ∈ v := by
  obtain ⟨i, j, hij, d, hd, e, he, hde⟩ := shared_distinct_faces P hlen
  have hdis := ho.distinct_faces_disjoint hij
  have hneq : P.get i ≠ P.get j := by
    intro heq
    exact List.disjoint_left.mp hdis hd (heq ▸ hd)
  rcases d with ⟨a, s⟩
  rcases e with ⟨a', t⟩
  dsimp at hde
  subst a'
  cases s <;> cases t
  · exact False.elim (List.disjoint_left.mp hdis hd he)
  · exact ⟨_, List.get_mem _ j, _, List.get_mem _ i, a, hneq.symm, he, hd⟩
  · exact ⟨_, List.get_mem _ i, _, List.get_mem _ j, a, hneq, hd, he⟩
  · exact False.elim (List.disjoint_left.mp hdis hd he)

private theorem face_merge_position {P : Presentation} (ho : Oriented P)
    [PreconnectedSpace (Realization P)] (hlen : 2 ≤ P.length)
    (hthree : ∀ w ∈ P, 3 ≤ w.length) :
    ∃ (a : ℕ) (U V : Word) (R : Presentation),
      Reindexed P ((U ++ [(a, true)]) :: ((a, false) :: V) :: R) ∧
      2 ≤ U.length ∧ 2 ≤ V.length ∧ ∀ w ∈ R, 3 ≤ w.length := by
  obtain ⟨u, hu, v, hv, a, hne, hau, hav⟩ := oriented_shared_faces ho hlen
  obtain ⟨R, hp⟩ := perm_two_to_front hu hv hne
  obtain ⟨L, X, hlu, _⟩ := List.eq_append_cons_of_mem hau
  obtain ⟨M, Y, hlv, _⟩ := List.eq_append_cons_of_mem hav
  have hru : List.IsRotated u ((X ++ L) ++ [(a, true)]) := by
    rw [hlu]
    simpa [List.append_assoc] using
      (List.isRotated_append (l := L ++ [(a, true)]) (l' := X))
  have hrv : List.IsRotated v ((a, false) :: (Y ++ M)) := by
    rw [hlv]
    simpa [List.append_assoc] using
      (List.isRotated_append (l := M) (l' := (a, false) :: Y))
  refine ⟨a, X ++ L, Y ++ M, R, ?_, ?_, ?_, ?_⟩
  · exact (reindexed_of_perm hp).trans
      ((Reindexed.rotate_head hru).trans ((Reindexed.rotate_head hrv).cons _))
  · have h := hthree u hu
    rw [hlu] at h
    simp only [List.length_append, List.length_cons] at h ⊢
    omega
  · have h := hthree v hv
    rw [hlv] at h
    simp only [List.length_append, List.length_cons] at h ⊢
    omega
  · intro w hw
    exact hthree w (hp.mem_iff.mpr (by simp [hw]))

private theorem Oriented.merge_fresh {U V : Word} {R : Presentation} {a : ℕ}
    (ho : Oriented ((U ++ [(a, true)]) :: ((a, false) :: V) :: R)) :
    a ∉ labels ((U ++ V) :: R) := by
  intro ha
  simp only [labels, occurrences, List.mem_toFinset, List.mem_map] at ha
  obtain ⟨⟨a', s⟩, hm, he⟩ := ha
  dsimp at he
  subst a'
  have hc := ho.count_le_one (a, s)
  have hm' := List.count_pos_iff.mpr hm
  simp only [occurrences, List.flatten_cons, List.count_append, List.count_cons] at hc hm'
  cases s <;> simp at hc <;> omega

/-- A connected oriented presentation whose faces have at least three sides
admits a proper merge of two faces. Source: Gallier–Xu Lemma 6.1 Step 3,
p.94. Connectedness supplies distinct faces sharing a label; uniqueness of
signed occurrences puts its two signs in opposite faces. Rotate these to the
last and first positions, then apply the inverse face subdivision. Both
remaining paths have at least two sides, so the move is proper. -/
theorem merge_two_faces (P : Presentation) (ho : Oriented P)
    [PreconnectedSpace (Realization P)] (hlen : 2 ≤ P.length)
    (hthree : ∀ w ∈ P, 3 ≤ w.length) :
    ∃ Q, PresentationEquivalent P Q ∧ Oriented Q ∧ Q.length + 1 = P.length ∧
      (∀ w ∈ Q, 3 ≤ w.length) ∧ (∀ d, UnpairedDart P d → UnpairedDart Q d) := by
  obtain ⟨a, U, V, R, hr, hU, hV, hR⟩ := face_merge_position ho hlen hthree
  have ho' := ho.reindexed hr
  have hnU : U ≠ [] := by intro h; simp [h] at hU
  have hnV : V ≠ [] := by intro h; simp [h] at hV
  have hf := Elementary.face [] R U V a hnU hnV ho'.merge_fresh
  refine ⟨(U ++ V) :: R, ?_, ho'.merge hnU, ?_, ?_, ?_⟩
  · exact (Elementary.reindex hr).equivalent.trans (by simpa using hf.equivalent.symm)
  · obtain ⟨e, _⟩ := hr
    have hlen := Fintype.card_congr e
    simpa using hlen.symm
  · intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · simp only [List.length_append]
      omega
    · exact hR w hw
  · intro d hd
    exact unpaired_merge a U V R d ((hr.unpaired d).mp hd)

/-- Merge the finite connected face graph to one polygon using only proper
P2 moves. Source: Gallier–Xu Lemma 6.1 Step 3, p.94. Induct on the number
of faces. A merge deletes one face and preserves at least three sides per
face; its realized homeomorphism preserves connectedness for the next step. -/
theorem merge_all_faces (P : Presentation) (hne : P ≠ []) (ho : Oriented P)
    [PreconnectedSpace (Realization P)] (hthree : ∀ w ∈ P, 3 ≤ w.length) :
    ∃ w, PresentationEquivalent P [w] ∧ Oriented [w] ∧ 3 ≤ w.length ∧
      (∀ d, UnpairedDart P d → UnpairedDart [w] d) := by
  generalize hn : P.length = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hlen : 2 ≤ P.length
    · obtain ⟨Q, he, hQ, hlenQ, hthreeQ, hboundaryQ⟩ := merge_two_faces P ho hlen hthree
      obtain ⟨sq⟩ := he
      let : PreconnectedSpace (Realization Q) :=
        sq.homeomorph.surjective.denseRange.preconnectedSpace sq.homeomorph.continuous
      have hneQ : Q ≠ [] := by intro he; simp [he] at hlenQ; omega
      obtain ⟨w, hw, how, hlenw, hboundaryw⟩ := ih Q.length (by omega) Q hneQ hQ hthreeQ rfl
      exact ⟨w, (show PresentationEquivalent P Q from ⟨sq⟩).trans hw, how, hlenw,
        fun d hd ↦ hboundaryw d (hboundaryQ d hd)⟩
    · cases P with
      | nil => exact False.elim (hne rfl)
      | cons w R =>
        have hR : R = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen; omega)
        subst R
        exact ⟨w, PresentationEquivalent.refl _, ho, hthree w (by simp), fun d hd ↦ hd⟩

/-- The original coherently oriented triangle presentation reduces to one
oriented polygon. Source: Gallier–Xu Lemma 6.1 Step 3, p.94. The original
carrier supplies connectedness and a point in the quotient. Every original
face has three sides, so the proper face-merging induction applies. -/
theorem triangle_presentation_one_face {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (hconnected : IsConnected (carrier K))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (horiented : Oriented (trianglePresentation K o))
    (H₀ : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o)) :
    ∃ w, PresentationEquivalent (trianglePresentation K o) [w] ∧
      Oriented [w] ∧ 3 ≤ w.length ∧
      (∀ d, UnpairedDart (trianglePresentation K o) d → UnpairedDart [w] d) := by
  let : PreconnectedSpace ↥(carrier K) := Subtype.preconnectedSpace hconnected.isPreconnected
  let : PreconnectedSpace (Realization (trianglePresentation K o)) :=
    H₀.surjective.denseRange.preconnectedSpace H₀.continuous
  refine merge_all_faces _ ?_ horiented ?_
  · obtain ⟨x, hx⟩ := hconnected.nonempty
    obtain ⟨y, hy⟩ := Quotient.exists_rep (H₀ ⟨x, hx⟩)
    intro he
    have hi := y.1.isLt
    have hzero : (trianglePresentation K o).length = 0 := congrArg List.length he
    omega
  · intro w hw
    simp only [trianglePresentation, List.mem_map] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    exact le_of_eq (HolomorphicAnosov.Topology.triangleWord_length_g9 _ _).symm

/-- Contract consecutive unpaired sides by the inverse of a genuine edge
subdivision. Source: Gallier–Xu Definition 6.3(P1), p.84, and Lemma 6.1
Step 2, pp.93–94. The two old labels occur only in the displayed positions,
so the global subdivision of the replacement label reproduces the entire
original presentation. -/
theorem boundary_path_contraction (a b c : ℕ) (X : Word) (hab : a ≠ b)
    (ha : a ∉ labels [X]) (hb : b ∉ labels [X]) (hc : c ∉ labels [X])
    (hca : c ≠ a) (hcb : c ≠ b) :
    PresentationEquivalent [(a, true) :: (b, true) :: X] [(c, true) :: X] := by
  have hsub : subdivideEdge [(c, true) :: X] c a b = [(a, true) :: (b, true) :: X] := by
    change [((c, true) :: X).flatMap (splitDart c a b)] = _
    rw [List.flatMap_cons, splitWord_unchanged c a b X
      (fun d hd ↦ fresh_dart [X] hc (by simp) hd)]
    simp [splitDart]
  rw [← hsub]
  apply Elementary.equivalent
  apply Elementary.inverse
  apply Elementary.edge
  · simp [labels, occurrences]
  · simpa [labels, occurrences, Ne.symm hca] using ha
  · simpa [labels, occurrences, Ne.symm hcb] using hb
  · exact hab

/-- Contract a full two-side paired path by inverse edge subdivision.
Source: Gallier–Xu Definition 6.3(P1), p.84. The reversed path is present
with reversed signs, and the two labels have no other occurrences; replacing
both paths is therefore exactly the inverse of a global P1 move. -/
theorem paired_path_contraction (a b c : ℕ) (U V : Word) (hab : a ≠ b)
    (ha : a ∉ labels [U, V]) (hb : b ∉ labels [U, V]) (hc : c ∉ labels [U, V])
    (hca : c ≠ a) (hcb : c ≠ b) :
    PresentationEquivalent [(a, true) :: (b, true) :: (U ++ (b, false) :: (a, false) :: V)]
      [(c, true) :: (U ++ (c, false) :: V)] := by
  have hU := splitWord_unchanged c a b U
    (fun d hd ↦ fresh_dart [U, V] hc (by simp) hd)
  have hV := splitWord_unchanged c a b V
    (fun d hd ↦ fresh_dart [U, V] hc (by simp) hd)
  have hsub : subdivideEdge [(c, true) :: (U ++ (c, false) :: V)] c a b =
      [(a, true) :: (b, true) :: (U ++ (b, false) :: (a, false) :: V)] := by
    change [((c, true) :: (U ++ (c, false) :: V)).flatMap (splitDart c a b)] = _
    simp only [List.flatMap_cons, List.flatMap_append, hU, hV]
    simp [splitDart]
  rw [← hsub]
  apply Elementary.equivalent
  apply Elementary.inverse
  apply Elementary.edge
  · simp [labels, occurrences]
  · simpa [labels, occurrences, Ne.symm hca, List.mem_map, List.mem_append,
      and_comm, and_left_comm, and_assoc] using ha
  · simpa [labels, occurrences, Ne.symm hcb, List.mem_map, List.mem_append,
      and_comm, and_left_comm, and_assoc] using hb
  · exact hab

private theorem cyclic_word_next {α : Type*} (a : α) (X : List α)
    (i : Fin (a :: X).length) :
    ((a :: X) ++ [a])[i.val + 1]'(by simp; omega) =
      (a :: X).get (finRotate (a :: X).length i) := by
  by_cases hi : i.val < X.length
  · have hr : finRotate (a :: X).length i = ⟨i.val + 1, by simp; omega⟩ :=
      finRotate_of_lt hi
    rw [hr, List.getElem_append_left (by simp; omega)]
    rfl
  · have he : i.val = X.length := by have := i.isLt; simp only [List.length_cons] at this; omega
    have hi' : i = ⟨X.length, by simp⟩ := Fin.ext he
    rw [hi']
    simp only [List.length_cons, finRotate_last']
    rw [List.getElem_append_right (by simp)]
    simp

private theorem cyclic_word_chain {α : Type*} (R : α → α → Prop) (a : α) (X : List α) :
    (∀ i : Fin (a :: X).length,
      R ((a :: X).get i) ((a :: X).get (finRotate (a :: X).length i))) ↔
      List.IsChain R ((a :: X) ++ [a]) := by
  rw [List.isChain_iff_getElem]
  constructor
  · intro h i hi
    have hi' : i < (a :: X).length := by simp only [List.length_append, List.length_singleton] at hi; omega
    have he := cyclic_word_next a X ⟨i, hi'⟩
    rw [List.getElem_append_left hi', he]
    exact h ⟨i, hi'⟩
  · intro h i
    have hi : i.val + 1 < ((a :: X) ++ [a]).length := by simpa using Nat.succ_lt_succ i.isLt
    have he := h i.val hi
    rw [List.getElem_append_left i.isLt, cyclic_word_next] at he
    exact he

/-- A map on incoming darts is constant on polygon corners precisely when
successive letters, including the closing pair, satisfy the incoming-dart
identity. Source: Gallier–Xu Definition 6.2, pp.81–83. This converts the
cyclic index definition to the finite chain of consecutive word positions. -/
theorem corner_compatible_chain {α : Type*} (f : Dart → α) (a : Dart) (X : Word) :
    (∀ d e, corner [a :: X] d e → f d = f e) ↔
      List.IsChain (fun d e ↦ f d = f (inverse e)) ((a :: X) ++ [a]) := by
  rw [← cyclic_word_chain]
  constructor
  · intro h i
    exact h _ _ ⟨0, i, rfl, rfl⟩
  · intro h d e hde
    obtain ⟨j, i, hd, he⟩ := hde
    have hj : j = 0 := Fin.eq_zero j
    subst j
    subst d
    subst e
    exact h i

private theorem sameVertex_map_eq {α : Type*} {P : Presentation} (f : Dart → α)
    (hf : ∀ d e, corner P d e → f d = f e) {d e : Dart}
    (h : sameVertex P d e) : f d = f e := by
  induction h with
  | rel d e h => exact hf d e h
  | refl d => rfl
  | symm d e h ih => exact ih.symm
  | trans d e u h h' ih ih' => exact ih.trans ih'

private theorem incoming_chain_constant {α : Type*} (f : Dart → α) (c : α)
    (a b : Dart) (X : Word) (ha : f a = c) (hb : f (inverse b) = c)
    (hX : ∀ d ∈ X, f d = c ∧ f (inverse d) = c) :
    List.IsChain (fun d e ↦ f d = f (inverse e)) (a :: (X ++ [b])) := by
  induction X generalizing a with
  | nil => simpa using ha.trans hb.symm
  | cons d X ih =>
    rw [List.cons_append, List.isChain_cons_cons]
    have hd := hX d (by simp)
    exact ⟨ha.trans hd.2.symm, ih d hd.1 (fun e he ↦ hX e (by simp [he]))⟩

/-- A paired side not crossed by any other label has distinct incoming
vertex classes at its two ends. Source: Gallier–Xu Lemma 6.1 Step 5,
p.95, with the incoming-neighbor inversion from Definition 6.2. Color the
darts in the first residual arc, together with the positive selected dart,
true; color all other darts false. Every corner preserves this color, while
the two selected darts have opposite colors. This remains valid when either
residual arc is empty. -/
theorem noninterlaced_edge_separates_vertices (a : ℕ) (X Y : Word)
    (ha : a ∉ labels [X, Y]) (hXY : Disjoint (labels [X]) (labels [Y])) :
    ¬ sameVertex [(a, true) :: (X ++ (a, false) :: Y)] (a, true) (a, false) := by
  let f : Dart → Bool := fun d ↦ decide (d = (a, true) ∨ d.1 ∈ labels [X])
  have haX : a ∉ labels [X] := by
    intro h
    apply ha
    simpa [labels, occurrences, List.mem_map, List.mem_append] using Or.inl h
  have haY : a ∉ labels [Y] := by
    intro h
    apply ha
    simpa [labels, occurrences, List.mem_map, List.mem_append] using Or.inr h
  have hp : f (a, true) = true := by simp [f]
  have hn : f (a, false) = false := by simp [f, haX]
  have hleft := incoming_chain_constant f true (a, true) (a, false) X hp
    (by simpa [inverse] using hp) (by
      intro d hd
      have hm : d.1 ∈ labels [X] := by simp only [labels, occurrences, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.mem_toFinset, List.mem_map]; exact ⟨d, hd, rfl⟩
      simp [f, inverse, hm])
  have hright := incoming_chain_constant f false (a, false) (a, true) Y hn
    (by simpa [inverse] using hn) (by
      intro d hd
      have hm : d.1 ∈ labels [Y] := by simp only [labels, occurrences, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.mem_toFinset, List.mem_map]; exact ⟨d, hd, rfl⟩
      have hnot : d.1 ∉ labels [X] := fun h ↦ Finset.disjoint_left.mp hXY h hm
      have hne : d.1 ≠ a := fresh_dart [Y] haY (by simp) hd
      rcases d with ⟨d, s⟩
      simp [f, inverse, hnot, hne])
  have hcompat : ∀ d e, corner [(a, true) :: (X ++ (a, false) :: Y)] d e → f d = f e := by
    apply (corner_compatible_chain f _ _).mpr
    simpa only [List.cons_append, List.append_assoc] using
      (List.isChain_cons_split.mpr ⟨hleft, hright⟩)
  intro h
  have he := sameVertex_map_eq f hcompat h
  rw [hp, hn] at he
  contradiction

/-- An oriented paired edge whose ends belong to the same vertex must be
interleaved with another paired label. Source: Gallier–Xu Lemma 6.1 Step 5,
p.95. Otherwise the two residual arcs have disjoint label sets, and the
corner-coloring separation contradicts equality of the endpoint classes.
Coherent orientation makes the two crossing occurrences have opposite signs. -/
theorem inner_loop_has_interleaving (a : ℕ) (X Y : Word)
    (ho : Oriented [(a, true) :: (X ++ (a, false) :: Y)])
    (hv : sameVertex [(a, true) :: (X ++ (a, false) :: Y)] (a, true) (a, false)) :
    ∃ (b : ℕ) (s : Bool) (U V Z T : Word), b ≠ a ∧
      X = U ++ (b, s) :: V ∧ Y = Z ++ (b, !s) :: T := by
  have ha : a ∉ labels [X, Y] := by
    have h := Oriented.paired_fresh (a := a) (U := X) (V := Y) (X := []) (by simpa using ho)
    simpa [labels, occurrences] using h
  have hcross : ¬Disjoint (labels [X]) (labels [Y]) := by
    intro hd
    exact noninterlaced_edge_separates_vertices a X Y ha hd hv
  obtain ⟨b, hbX, hbY⟩ := Finset.not_disjoint_iff.mp hcross
  have hba : b ≠ a := by
    intro he
    apply ha
    subst b
    simpa [labels, occurrences, List.mem_map, List.mem_append] using Or.inl hbX
  simp only [labels, occurrences, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.mem_toFinset, List.mem_map] at hbX hbY
  obtain ⟨⟨b', s⟩, hs, he⟩ := hbX
  obtain ⟨⟨b'', t⟩, ht, he'⟩ := hbY
  dsimp at he he'
  subst b'
  subst b''
  have hst : t = !s := by
    have hc := ho.count_le_one (b, s)
    have hcs := List.count_pos_iff.mpr hs
    by_contra hne
    have heq : t = s := by cases s <;> cases t <;> simp_all
    subst t
    have hct := List.count_pos_iff.mpr ht
    simp only [occurrences, List.flatten_cons, List.flatten_nil, List.count_append,
      List.count_cons, List.count_nil, Nat.add_zero] at hc
    omega
  subst t
  obtain ⟨U, V, hX, _⟩ := List.eq_append_cons_of_mem hs
  obtain ⟨Z, T, hY, _⟩ := List.eq_append_cons_of_mem ht
  exact ⟨b, s, U, V, Z, T, hba, hX, hY⟩

/-- The handle-extraction macro is independent of the chosen orientations
of its two labels. Reverse either label globally when needed; the residual
arcs do not use those labels, so they are fixed. Apply the three-interchange
positive-label macro to obtain the same handle and residual order. -/
theorem signed_interleaved_handle_extraction (a b : ℕ) (s t : Bool) (U V X Y : Word)
    (ha : a ∉ labels [U, V, X, Y]) (hb : b ∉ labels [U, V, X, Y]) (hab : a ≠ b) :
    ∃ e d : ℕ, e ≠ d ∧ e ∉ labels [U, V, X, Y] ∧ d ∉ labels [U, V, X, Y] ∧
      PresentationEquivalent
        [(a, s) :: (U ++ (b, t) :: (V ++ (a, !s) :: (X ++ (b, !t) :: Y)))]
        [(e, true) :: (d, false) :: (e, false) :: (d, true) :: (Y ++ X ++ V ++ U)] := by
  let flip : ℕ → Bool := fun k ↦ if k = a then !s else if k = b then !t else false
  have hmap (W : Word) (hW : W ∈ [U, V, X, Y]) :
      W.map (fun q ↦ ((Equiv.refl ℕ) q.1, if flip q.1 then !q.2 else q.2)) = W := by
    conv_rhs => rw [← List.map_id W]
    apply List.map_congr_left
    intro q hq
    have hqa := fresh_dart [U, V, X, Y] ha hW hq
    have hqb := fresh_dart [U, V, X, Y] hb hW hq
    simp [flip, hqa, hqb]
  have hr := rename_equivalent
    [(a, s) :: (U ++ (b, t) :: (V ++ (a, !s) :: (X ++ (b, !t) :: Y)))]
    (Equiv.refl ℕ) flip
  have he : PresentationEquivalent
      [(a, s) :: (U ++ (b, t) :: (V ++ (a, !s) :: (X ++ (b, !t) :: Y)))]
      [(a, true) :: (U ++ (b, true) :: (V ++ (a, false) :: (X ++ (b, false) :: Y)))] := by
    simp only [List.map_cons, List.map_append, List.map_nil] at hr
    rw [hmap U (by simp), hmap V (by simp), hmap X (by simp), hmap Y (by simp)] at hr
    cases s <;> cases t <;> simpa [flip, Ne.symm hab] using hr
  obtain ⟨e, d, hed, he', hd', h⟩ := interleaved_handle_extraction a b U V X Y ha hb hab
  exact ⟨e, d, hed, he', hd', he.trans h⟩

/-- Rotate the arc between the two occurrences of a paired edge while
retaining its original label. Source: Gallier–Xu Lemma 6.1 Step 4, p.94.
Perform the proper paired-edge interchange with a fresh cut label, then
exchange the unused old label with the new one and reverse its orientation. -/
theorem paired_arc_rotation (a : ℕ) (U V X : Word) (ha : a ∉ labels [U, V, X]) :
    PresentationEquivalent [(a, true) :: (U ++ V ++ (a, false) :: X)]
      [(a, true) :: (V ++ U ++ (a, false) :: X)] := by
  obtain ⟨c, hc⟩ := (insert a (labels [U, V, X])).exists_notMem
  simp only [Finset.mem_insert, not_or] at hc
  have hi := paired_edge_interchange a c U V X ha (by
    simpa [labels, occurrences, List.mem_map, List.mem_append,
      hc.1, and_comm, and_left_comm, and_assoc] using hc.2)
  have hmap (W : Word) (hW : W ∈ [U, V, X]) :
      W.map (fun q ↦ (Equiv.swap c a q.1, if decide (q.1 = c) then !q.2 else q.2)) = W := by
    conv_rhs => rw [← List.map_id W]
    apply List.map_congr_left
    intro q hq
    have hqa := fresh_dart [U, V, X] ha hW hq
    have hqc := fresh_dart [U, V, X] hc.2 hW hq
    simp [Equiv.swap_apply_of_ne_of_ne hqc hqa, hqc]
  have hr := rename_equivalent [(c, false) :: (V ++ U ++ (c, true) :: X)]
    (Equiv.swap c a) (fun k ↦ decide (k = c))
  simp only [List.map_cons, List.map_append, List.map_nil] at hr
  rw [hmap V (by simp), hmap U (by simp), hmap X (by simp)] at hr
  exact hi.trans (by simpa using hr)

/-- Either signed occurrence may serve as the initial side of an arc
rotation. Globally reverse the selected label before and after the positive
macro; all other occurrences are fixed by freshness. -/
theorem signed_paired_arc_rotation (a : ℕ) (s : Bool) (U V X : Word)
    (ha : a ∉ labels [U, V, X]) :
    PresentationEquivalent [(a, s) :: (U ++ V ++ (a, !s) :: X)]
      [(a, s) :: (V ++ U ++ (a, !s) :: X)] := by
  cases s
  · let flip : ℕ → Bool := fun k ↦ decide (k = a)
    have hmap (W : Word) (hW : W ∈ [U, V, X]) :
        W.map (fun q ↦ ((Equiv.refl ℕ) q.1, if flip q.1 then !q.2 else q.2)) = W := by
      conv_rhs => rw [← List.map_id W]
      apply List.map_congr_left
      intro q hq
      have hqa := fresh_dart [U, V, X] ha hW hq
      simp [flip, hqa]
    have hr := rename_equivalent [(a, false) :: (U ++ V ++ (a, true) :: X)]
      (Equiv.refl ℕ) flip
    have hr' := rename_equivalent [(a, false) :: (V ++ U ++ (a, true) :: X)]
      (Equiv.refl ℕ) flip
    simp only [List.map_cons, List.map_append, List.map_nil] at hr hr'
    rw [hmap U (by simp), hmap V (by simp), hmap X (by simp)] at hr hr'
    have h1 : PresentationEquivalent [(a, false) :: (U ++ V ++ (a, true) :: X)]
        [(a, true) :: (U ++ V ++ (a, false) :: X)] := by simpa [flip] using hr
    have h2 : PresentationEquivalent [(a, false) :: (V ++ U ++ (a, true) :: X)]
        [(a, true) :: (V ++ U ++ (a, false) :: X)] := by simpa [flip] using hr'
    exact h1.trans ((paired_arc_rotation a U V X ha).trans h2.symm)
  · exact paired_arc_rotation a U V X ha

/-- A completed boundary-loop block allows a cyclic change of starting
position in the remaining word. Source: Gallier–Xu Lemma 6.1 Step 6,
p.95. Start at the inverse spoke, rotate the outer arc by the proper
paired-edge macro, and return to the original block's first side. -/
theorem loop_residual_rotation (a b : ℕ) (s t : Bool) (X Y : Word)
    (ha : a ∉ labels [X, Y]) (hab : a ≠ b) :
    PresentationEquivalent [(a, s) :: (b, t) :: (a, !s) :: (X ++ Y)]
      [(a, s) :: (b, t) :: (a, !s) :: (Y ++ X)] := by
  have hi := signed_paired_arc_rotation a (!s) X Y [(b, t)] (by
    simpa [labels, occurrences, List.mem_map, List.mem_append,
      hab, and_comm, and_left_comm, and_assoc] using ha)
  have hr : PresentationEquivalent [(a, s) :: (b, t) :: (a, !s) :: (X ++ Y)]
      [(a, !s) :: (X ++ Y ++ [(a, s), (b, t)])] := by
    apply singleton_rotation
    simpa [List.append_assoc] using
      (List.isRotated_append (l := [(a, s), (b, t)]) (l' := (a, !s) :: (X ++ Y)))
  have hr' : PresentationEquivalent [(a, !s) :: (Y ++ X ++ [(a, s), (b, t)])]
      [(a, s) :: (b, t) :: (a, !s) :: (Y ++ X)] := by
    apply singleton_rotation
    simpa [List.append_assoc] using
      (List.isRotated_append (l := (a, !s) :: (Y ++ X)) (l' := [(a, s), (b, t)]))
  apply hr.trans
  apply PresentationEquivalent.trans (Q := [(a, !s) :: (Y ++ X ++ [(a, s), (b, t)])])
  · simpa [List.append_assoc] using hi
  exact hr'

/-- A completed handle block allows a cyclic change of starting position
in the remaining word. Source: the paired-edge interchange of Gallier–Xu
Lemma 6.1 Step 4, pp.94–95. Four arc rotations, successively at the inverse
first side, the second side, the first side, and the inverse second side,
move the chosen residual prefix past the handle without changing its labels.
Each rotation is already a finite sequence of proper realized moves. -/
theorem handle_residual_rotation (a b : ℕ) (s t : Bool) (X Y : Word)
    (ha : a ∉ labels [X, Y]) (hb : b ∉ labels [X, Y]) (hab : a ≠ b) :
    PresentationEquivalent [(a, s) :: (b, t) :: (a, !s) :: (b, !t) :: (X ++ Y)]
      [(a, s) :: (b, t) :: (a, !s) :: (b, !t) :: (Y ++ X)] := by
  have h1 := signed_paired_arc_rotation a (!s) ((b, !t) :: X) Y [(b, t)] (by
    simpa [labels, occurrences, List.mem_map, List.mem_append,
      hab, and_comm, and_left_comm, and_assoc] using ha)
  have h2 := signed_paired_arc_rotation b t [(a, !s)] Y (X ++ [(a, s)]) (by
    simpa [labels, occurrences, List.mem_map, List.mem_append,
      Ne.symm hab, and_comm, and_left_comm, and_assoc] using hb)
  have h3 := signed_paired_arc_rotation a s [(b, t)] Y ((b, !t) :: X) (by
    simpa [labels, occurrences, List.mem_map, List.mem_append,
      hab, and_comm, and_left_comm, and_assoc] using ha)
  have h4 := signed_paired_arc_rotation b (!t) (X ++ [(a, s)]) Y [(a, !s)] (by
    simpa [labels, occurrences, List.mem_map, List.mem_append,
      Ne.symm hab, and_comm, and_left_comm, and_assoc] using hb)
  have r0 : PresentationEquivalent
      [(a, s) :: (b, t) :: (a, !s) :: (b, !t) :: (X ++ Y)]
      [(a, !s) :: (b, !t) :: (X ++ Y ++ [(a, s), (b, t)])] := by
    apply singleton_rotation
    simpa [List.append_assoc] using (List.isRotated_append
      (l := [(a, s), (b, t)]) (l' := (a, !s) :: (b, !t) :: (X ++ Y)))
  have r1 : PresentationEquivalent
      [(a, !s) :: (Y ++ (b, !t) :: (X ++ [(a, s), (b, t)]))]
      [(b, t) :: (a, !s) :: (Y ++ (b, !t) :: (X ++ [(a, s)]))] := by
    apply singleton_rotation
    simpa [List.append_assoc] using (List.isRotated_append
      (l := (a, !s) :: (Y ++ (b, !t) :: (X ++ [(a, s)]))) (l' := [(b, t)]))
  have r2 : PresentationEquivalent
      [(b, t) :: (Y ++ (a, !s) :: (b, !t) :: (X ++ [(a, s)]))]
      [(a, s) :: (b, t) :: (Y ++ (a, !s) :: (b, !t) :: X)] := by
    apply singleton_rotation
    simpa [List.append_assoc] using (List.isRotated_append
      (l := (b, t) :: (Y ++ (a, !s) :: (b, !t) :: X)) (l' := [(a, s)]))
  have r3 : PresentationEquivalent
      [(a, s) :: (Y ++ (b, t) :: (a, !s) :: (b, !t) :: X)]
      [(b, !t) :: (X ++ (a, s) :: (Y ++ [(b, t), (a, !s)]))] := by
    apply singleton_rotation
    simpa [List.append_assoc] using (List.isRotated_append
      (l := (a, s) :: (Y ++ [(b, t), (a, !s)])) (l' := (b, !t) :: X))
  have r4 : PresentationEquivalent
      [(b, !t) :: (Y ++ X ++ [(a, s), (b, t), (a, !s)])]
      [(a, s) :: (b, t) :: (a, !s) :: (b, !t) :: (Y ++ X)] := by
    apply singleton_rotation
    simpa [List.append_assoc] using (List.isRotated_append
      (l := (b, !t) :: (Y ++ X)) (l' := [(a, s), (b, t), (a, !s)]))
  apply r0.trans
  apply PresentationEquivalent.trans (Q := [(a, !s) :: (Y ++ (b, !t) :: (X ++ [(a, s), (b, t)]))])
  · simpa [List.append_assoc] using h1
  apply r1.trans
  apply PresentationEquivalent.trans (Q := [(b, t) :: (Y ++ (a, !s) :: (b, !t) :: (X ++ [(a, s)]))])
  · simpa [List.append_assoc] using h2
  apply r2.trans
  apply PresentationEquivalent.trans (Q := [(a, s) :: (Y ++ (b, t) :: (a, !s) :: (b, !t) :: X)])
  · simpa [List.append_assoc] using h3
  apply r3.trans
  apply PresentationEquivalent.trans (Q := [(b, !t) :: (Y ++ X ++ [(a, s), (b, t), (a, !s)])])
  · simpa [List.append_assoc] using h4
  exact r4

private theorem inverse_inverse (a : Dart) : inverse (inverse a) = a := by
  rcases a with ⟨a, s⟩
  simp [inverse]

private theorem inverse_ne_self (a : Dart) : inverse a ≠ a := by
  rcases a with ⟨a, s⟩
  cases s <;> simp [inverse]

private theorem pair_word_decomposition (W : Word) (a : Dart)
    (ha : a ∈ W) (hai : inverse a ∈ W) :
    ∃ (d : Dart) (L U R : Word), W = L ++ d :: (U ++ inverse d :: R) := by
  obtain ⟨L, R, hW, _⟩ := List.eq_append_cons_of_mem ha
  rw [hW] at hai
  simp only [List.mem_append, List.mem_cons] at hai
  rcases hai with hi | he | hi
  · obtain ⟨J, K, hL, _⟩ := List.eq_append_cons_of_mem hi
    refine ⟨inverse a, J, K, R, ?_⟩
    rw [hW, hL, inverse_inverse]
    simp [List.append_assoc]
  · exact False.elim (inverse_ne_self a he)
  · obtain ⟨J, K, hR, _⟩ := List.eq_append_cons_of_mem hi
    exact ⟨a, L, J, K, by rw [hW, hR]⟩

/-- A finite word containing a paired label has an innermost paired arc:
no label occurs with both signs strictly inside that arc. Source: the
finite paired-word reduction of Gallier–Xu Lemma 6.1 Steps 4–5, pp.94–95.
Choose a pair whose intervening substring has least length. An internal
pair would define a strictly shorter intervening substring, a contradiction. -/
theorem innermost_paired_arc (W : Word) (hpair : ∃ a ∈ W, inverse a ∈ W) :
    ∃ (a : Dart) (L U R : Word), W = L ++ a :: (U ++ inverse a :: R) ∧
      ∀ d ∈ U, inverse d ∉ U := by
  have hex : ∃ n : ℕ, ∃ (a : Dart) (L U R : Word),
      U.length = n ∧ W = L ++ a :: (U ++ inverse a :: R) := by
    obtain ⟨a, ha, hai⟩ := hpair
    obtain ⟨d, L, U, R, hW⟩ := pair_word_decomposition W a ha hai
    exact ⟨U.length, d, L, U, R, rfl, hW⟩
  obtain ⟨a, L, U, R, hlen, hW⟩ := Nat.find_spec hex
  refine ⟨a, L, U, R, hW, ?_⟩
  intro d hd hdi
  obtain ⟨e, J, V, K, hU⟩ := pair_word_decomposition U d hd hdi
  have hshort : V.length < U.length := by rw [hU]; simp only [List.length_append, List.length_cons]; omega
  have hmin : Nat.find hex ≤ V.length := Nat.find_min' hex ⟨e, L ++ a :: J, V,
    K ++ inverse a :: R, rfl, by rw [hW, hU]; simp [List.append_assoc]⟩
  omega

private theorem nodup_labels_of_unpaired (W : Word) (hW : W.Nodup)
    (hu : ∀ d ∈ W, inverse d ∉ W) : (W.map Prod.fst).Nodup := by
  induction W with
  | nil => simp
  | cons a W ih =>
    rw [List.nodup_cons] at hW
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hW.2 (fun d hd hdi ↦ hu d (by simp [hd]) (by simp [hdi]))⟩
    intro ha
    obtain ⟨d, hd, he⟩ := List.mem_map.mp ha
    have hneq : d ≠ a := fun he ↦ hW.1 (he ▸ hd)
    have hinv : d = inverse a := by
      rcases a with ⟨a, s⟩
      rcases d with ⟨d, t⟩
      dsimp at he
      subst d
      cases s <;> cases t <;> simp_all [inverse]
    exact hu a (by simp) (by simp [← hinv, hd])

/-- One completed orientable handle or boundary-loop block, retaining its
chosen side orientations. Source: Gallier–Xu Lemma 6.1 Steps 4–6, pp.94–95. -/
private structure ReductionBlock where
  isHandle : Bool
  a : Dart
  b : Dart
  distinct : a.1 ≠ b.1

private def ReductionBlock.word (B : ReductionBlock) : Word :=
  if B.isHandle then [B.a, B.b, inverse B.a, inverse B.b]
  else [B.a, B.b, inverse B.a]

private def blocksWord (B : List ReductionBlock) : Word := B.flatMap ReductionBlock.word

private def blocksLabels (B : List ReductionBlock) : List ℕ :=
  B.flatMap fun q ↦ [q.a.1, q.b.1]

private theorem ReductionBlock.residual_rotation (B : ReductionBlock) (X Y : Word)
    (ha : B.a.1 ∉ labels [X, Y]) (hb : B.b.1 ∉ labels [X, Y]) :
    PresentationEquivalent [B.word ++ X ++ Y] [B.word ++ Y ++ X] := by
  rcases B with ⟨k, ⟨a, s⟩, ⟨b, t⟩, hab⟩
  cases k
  · simpa [ReductionBlock.word, inverse, List.append_assoc] using
      loop_residual_rotation a b s t X Y ha hab
  · simpa [ReductionBlock.word, inverse, List.append_assoc] using
      handle_residual_rotation a b s t X Y ha hb hab

private theorem ReductionBlock.move_left (B : ReductionBlock) (L R : Word)
    (ha : B.a.1 ∉ labels [L, R]) (hb : B.b.1 ∉ labels [L, R]) :
    PresentationEquivalent [L ++ B.word ++ R] [B.word ++ L ++ R] := by
  have hr : PresentationEquivalent [L ++ B.word ++ R] [B.word ++ R ++ L] := by
    apply singleton_rotation
    simpa [List.append_assoc] using (List.isRotated_append (l := L) (l' := B.word ++ R))
  exact hr.trans (B.residual_rotation R L
    (by simpa [labels, occurrences, List.mem_map, List.mem_append, or_comm] using ha)
    (by simpa [labels, occurrences, List.mem_map, List.mem_append, or_comm] using hb))

private theorem ReductionBlock.move_left_context (B : ReductionBlock) (C L R : Word)
    (ha : B.a.1 ∉ labels [C, L, R]) (hb : B.b.1 ∉ labels [C, L, R]) :
    PresentationEquivalent [C ++ L ++ B.word ++ R] [C ++ B.word ++ L ++ R] := by
  have r1 : PresentationEquivalent [C ++ L ++ B.word ++ R] [L ++ B.word ++ (R ++ C)] := by
    apply singleton_rotation
    simpa [List.append_assoc] using (List.isRotated_append (l := C) (l' := L ++ B.word ++ R))
  have hm := B.move_left L (R ++ C)
    (by simpa [labels, occurrences, List.mem_map, List.mem_append,
      or_comm, or_left_comm, or_assoc] using ha)
    (by simpa [labels, occurrences, List.mem_map, List.mem_append,
      or_comm, or_left_comm, or_assoc] using hb)
  have r2 : PresentationEquivalent [B.word ++ L ++ (R ++ C)] [C ++ B.word ++ L ++ R] := by
    apply singleton_rotation
    simpa [List.append_assoc] using (List.isRotated_append (l := B.word ++ L ++ R) (l' := C))
  exact r1.trans (hm.trans r2)

/-- Spur cancellation inside an arbitrary surviving word. Source:
Seifert–Threlfall §38 Step 2, p.140. Rotate the two spur sides to the
front, perform the proper finite cancellation, then restore the starting
position. The surviving context is explicitly required to be nonempty. -/
theorem contextual_spur_cancellation (a : Dart) (L R : Word)
    (hLR : L ++ R ≠ []) (ha : a.1 ∉ labels [L, R]) :
    PresentationEquivalent [L ++ a :: inverse a :: R] [L ++ R] := by
  have r1 : PresentationEquivalent [L ++ a :: inverse a :: R] [a :: inverse a :: (R ++ L)] := by
    apply singleton_rotation
    simpa [List.append_assoc] using (List.isRotated_append (l := L) (l' := a :: inverse a :: R))
  have hs := signed_spur_cancellation a (R ++ L)
    (by simpa [List.append_eq_nil_iff, and_comm] using hLR)
    (by simpa [labels, occurrences, List.mem_map, List.mem_append, or_comm] using ha)
  exact r1.trans (hs.trans (singleton_rotation (List.isRotated_append (l := R) (l' := L))))

/-- Contract two adjacent unpaired boundary sides in any context and with
either orientation. Source: Gallier–Xu Definition 6.3(P1), p.84, and
Lemma 6.1 Step 2, pp.93–94. Reverse the two used label orientations if
necessary, rotate them to the first positions, apply inverse P1, and restore
the starting position. Freshness fixes every side in the surviving context. -/
theorem contextual_boundary_contraction (a b : Dart) (c : ℕ) (L R : Word)
    (hab : a.1 ≠ b.1) (ha : a.1 ∉ labels [L, R]) (hb : b.1 ∉ labels [L, R])
    (hc : c ∉ labels [L, R]) (hca : c ≠ a.1) (hcb : c ≠ b.1) :
    PresentationEquivalent [L ++ a :: b :: R] [L ++ (c, true) :: R] := by
  rcases a with ⟨a, s⟩
  rcases b with ⟨b, t⟩
  let flip : ℕ → Bool := fun k ↦ if k = a then !s else if k = b then !t else false
  have hmap : (R ++ L).map
      (fun q ↦ ((Equiv.refl ℕ) q.1, if flip q.1 then !q.2 else q.2)) = R ++ L := by
    conv_rhs => rw [← List.map_id (R ++ L)]
    apply List.map_congr_left
    intro q hq
    have hm : q ∈ occurrences [L, R] := by simpa [occurrences, List.mem_append, or_comm] using hq
    have hqa : q.1 ≠ a := by
      intro he
      apply ha
      simp only [labels, List.mem_toFinset, List.mem_map]
      exact ⟨q, hm, he⟩
    have hqb : q.1 ≠ b := by
      intro he
      apply hb
      simp only [labels, List.mem_toFinset, List.mem_map]
      exact ⟨q, hm, he⟩
    simp [flip, hqa, hqb]
  have hr := rename_equivalent [(a, s) :: (b, t) :: (R ++ L)] (Equiv.refl ℕ) flip
  simp only [List.map_cons, List.map_nil] at hr
  rw [hmap] at hr
  have hr' : PresentationEquivalent [(a, s) :: (b, t) :: (R ++ L)]
      [(a, true) :: (b, true) :: (R ++ L)] := by
    cases s <;> cases t <;> simpa [flip, Ne.symm hab] using hr
  have hc' := boundary_path_contraction a b c (R ++ L) hab
    (by simpa [labels, occurrences, List.mem_map, List.mem_append, or_comm] using ha)
    (by simpa [labels, occurrences, List.mem_map, List.mem_append, or_comm] using hb)
    (by simpa [labels, occurrences, List.mem_map, List.mem_append, or_comm] using hc) hca hcb
  have r1 : PresentationEquivalent [L ++ (a, s) :: (b, t) :: R]
      [(a, s) :: (b, t) :: (R ++ L)] := by
    apply singleton_rotation
    simpa [List.append_assoc] using
      (List.isRotated_append (l := L) (l' := (a, s) :: (b, t) :: R))
  have r2 : PresentationEquivalent [(c, true) :: (R ++ L)] [L ++ (c, true) :: R] := by
    apply singleton_rotation
    exact List.isRotated_append (l := (c, true) :: R) (l' := L)
  exact r1.trans (hr'.trans (hc'.trans r2))

private theorem contextual_handle_extraction (a b : Dart) (L U V X Y : Word)
    (ha : a.1 ∉ labels [L, U, V, X, Y]) (hb : b.1 ∉ labels [L, U, V, X, Y])
    (hab : a.1 ≠ b.1) :
    ∃ B : ReductionBlock, B.isHandle = true ∧
      B.a.1 ∉ labels [L, U, V, X, Y] ∧ B.b.1 ∉ labels [L, U, V, X, Y] ∧
      PresentationEquivalent [L ++ a :: (U ++ b :: (V ++ inverse a :: (X ++ inverse b :: Y)))]
        [B.word ++ L ++ X ++ V ++ U ++ Y] := by
  rcases a with ⟨a, s⟩
  rcases b with ⟨b, t⟩
  obtain ⟨e, d, hed, he, hd, hi⟩ := signed_interleaved_handle_extraction a b s t U V X (Y ++ L)
    (by simpa [labels, occurrences, List.mem_map, List.mem_append,
      or_comm, or_left_comm, or_assoc] using ha)
    (by simpa [labels, occurrences, List.mem_map, List.mem_append,
      or_comm, or_left_comm, or_assoc] using hb) hab
  let B : ReductionBlock := ⟨true, (e, true), (d, false), hed⟩
  refine ⟨B, rfl, ?_, ?_, ?_⟩
  · simpa [B, labels, occurrences, List.mem_map, List.mem_append,
      or_comm, or_left_comm, or_assoc] using he
  · simpa [B, labels, occurrences, List.mem_map, List.mem_append,
      or_comm, or_left_comm, or_assoc] using hd
  have r1 : PresentationEquivalent
      [L ++ (a, s) :: (U ++ (b, t) :: (V ++ inverse (a, s) :: (X ++ inverse (b, t) :: Y)))]
      [(a, s) :: (U ++ (b, t) :: (V ++ (a, !s) :: (X ++ (b, !t) :: (Y ++ L))))] := by
    apply singleton_rotation
    simpa [inverse, List.append_assoc] using (List.isRotated_append (l := L)
      (l' := (a, s) :: (U ++ (b, t) :: (V ++ inverse (a, s) :: (X ++ inverse (b, t) :: Y)))))
  have hr := B.residual_rotation Y (L ++ X ++ V ++ U)
    (by simpa [B, labels, occurrences, List.mem_map, List.mem_append,
      or_comm, or_left_comm, or_assoc] using he)
    (by simpa [B, labels, occurrences, List.mem_map, List.mem_append,
      or_comm, or_left_comm, or_assoc] using hd)
  apply r1.trans
  apply PresentationEquivalent.trans (Q := [B.word ++ Y ++ (L ++ X ++ V ++ U)])
  · simpa [B, ReductionBlock.word, inverse, List.append_assoc] using hi
  simpa [List.append_assoc] using hr

private theorem paired_label_fresh (a : Dart) (L U R : Word)
    (hnd : (L ++ a :: (U ++ inverse a :: R)).Nodup) : a.1 ∉ labels [L, U, R] := by
  intro ha
  simp only [labels, occurrences, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.mem_toFinset, List.mem_map, List.mem_append] at ha
  obtain ⟨⟨k, t⟩, hm, he⟩ := ha
  rcases a with ⟨a, s⟩
  dsimp at he
  subst k
  have hp := List.nodup_iff_count.mp hnd (a, true)
  have hn := List.nodup_iff_count.mp hnd (a, false)
  simp only [List.count_append, List.count_cons, inverse] at hp hn
  cases s <;> simp at hp hn
  all_goals rcases hm with hm | hm | hm <;> cases t
  all_goals have hc := List.count_pos_iff.mpr hm
  all_goals omega

private def WordReductionCase (W : Word) : Prop :=
  W.length ≤ 1 ∨
  (∃ (a : Dart) (L R : Word), W = L ++ a :: inverse a :: R) ∨
  (∃ (a b : Dart) (L R : Word), W = L ++ a :: b :: R ∧
    inverse a ∉ W ∧ inverse b ∉ W) ∨
  (∃ (a b : Dart) (L R : Word), W = L ++ a :: b :: inverse a :: R ∧ inverse b ∉ W) ∨
  (∃ (a b : Dart) (L U V X Y : Word),
    W = L ++ a :: (U ++ b :: (V ++ inverse a :: (X ++ inverse b :: Y))))

/-- Finite case selection for orientable word normalization. Source:
Gallier–Xu Lemma 6.1 Steps 1, 2, 4 and 5, pp.92–95. Choose a paired arc
with shortest interior. If an interior letter is paired in the whole word,
its opposite lies outside the arc and supplies an interleaving. Otherwise
all interior letters are unpaired: zero letters give a spur, one gives a
boundary-loop block, and two or more give adjacent unpaired sides to
contract. If there is no paired label anywhere, a word of length at least
two itself has adjacent unpaired sides. Every case strictly reduces the
active word once the displayed completed block is removed. -/
private theorem word_reduction_case (W : Word) (hnd : W.Nodup) : WordReductionCase W := by
  by_cases hp : ∃ a ∈ W, inverse a ∈ W
  · obtain ⟨a, L, U, R, hW, hU⟩ := innermost_paired_arc W hp
    have ha : a.1 ∉ labels [L, U, R] := paired_label_fresh a L U R (hW ▸ hnd)
    by_cases hcross : ∃ d ∈ U, inverse d ∈ W
    · obtain ⟨d, hd, hdi⟩ := hcross
      obtain ⟨J, K, hUK, _⟩ := List.eq_append_cons_of_mem hd
      have hda := fresh_dart [L, U, R] ha (by simp) hd
      have hnea : inverse d ≠ a := by intro he; apply hda; simpa [inverse] using congrArg (fun q : Dart ↦ q.1) he
      have hneai : inverse d ≠ inverse a := by intro he; apply hda; simpa [inverse] using congrArg (fun q : Dart ↦ q.1) he
      have hdiU := hU d hd
      rw [hW] at hdi
      simp only [List.mem_append, List.mem_cons, hnea, hneai, hdiU,
        false_or] at hdi
      rcases hdi with hdi | hdi
      · obtain ⟨M, N, hL, _⟩ := List.eq_append_cons_of_mem hdi
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨inverse d, a, M, N, J, K, R,
          by rw [hW, hL, hUK, inverse_inverse]; simp [List.append_assoc]⟩)))
      · obtain ⟨X, Y, hR, _⟩ := List.eq_append_cons_of_mem hdi
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, d, L, J, K, X, Y,
          by rw [hW, hUK, hR]; simp [List.append_assoc]⟩)))
    · have hu : ∀ d ∈ U, inverse d ∉ W := by simpa only [not_exists, not_and] using hcross
      cases U with
      | nil => exact Or.inr (Or.inl ⟨a, L, R, by simpa using hW⟩)
      | cons d U =>
        cases U with
        | nil => exact Or.inr (Or.inr (Or.inr (Or.inl
            ⟨a, d, L, R, by simpa using hW, hu d (by simp)⟩)))
        | cons e U =>
          exact Or.inr (Or.inr (Or.inl ⟨d, e, L ++ [a], U ++ inverse a :: R,
            by simpa [List.append_assoc] using hW, hu d (by simp), hu e (by simp)⟩))
  · have hu : ∀ a ∈ W, inverse a ∉ W := by simpa only [not_exists, not_and] using hp
    cases W with
    | nil => exact Or.inl (by simp)
    | cons a W =>
      cases W with
      | nil => exact Or.inl (by simp)
      | cons b W => exact Or.inr (Or.inr (Or.inl
          ⟨a, b, [], W, rfl, hu a (by simp), hu b (by simp)⟩))

private theorem label_mem_word {k : ℕ} {W : Word} :
    k ∈ labels [W] ↔ ∃ d ∈ W, d.1 = k := by simp [labels, occurrences]

private theorem label_mem_append (k : ℕ) (U V : Word) :
    k ∈ labels [U ++ V] ↔ k ∈ labels [U] ∨ k ∈ labels [V] := by
  simp [labels, occurrences, List.mem_map]

private theorem ReductionBlock.label_mem_word (B : ReductionBlock) (k : ℕ) :
    k ∈ labels [B.word] ↔ k = B.a.1 ∨ k = B.b.1 := by
  rcases B with ⟨h, a, b, hab⟩
  cases h <;> simp [ReductionBlock.word, labels, occurrences, inverse, eq_comm, or_comm]

private theorem blocks_label_mem (B : List ReductionBlock) (k : ℕ) :
    k ∈ labels [blocksWord B] ↔ k ∈ blocksLabels B := by
  induction B with
  | nil => simp [blocksWord, blocksLabels, labels, occurrences]
  | cons b B ih =>
    change k ∈ labels [b.word ++ blocksWord B] ↔ k ∈ b.a.1 :: b.b.1 :: blocksLabels B
    rw [label_mem_append, b.label_mem_word, ih]
    simp [or_assoc]

private def OrderedBlocks (B : List ReductionBlock) : Prop :=
  B.Pairwise (fun x y ↦ y.isHandle = true → x.isHandle = true)

private def ReductionReady (B : List ReductionBlock) (z : Dart) (W : Word) : Prop :=
  (blocksLabels B).Nodup ∧ W.Nodup ∧ z.1 ∉ blocksLabels B ∧ z.1 ∉ labels [W] ∧
    ∀ k ∈ blocksLabels B, k ∉ labels [W]

private theorem ReductionReady.residual {B : List ReductionBlock} {z : Dart} {W V D : Word}
    (h : ReductionReady B z W) (hp : W.Perm (D ++ V)) : ReductionReady B z V := by
  rcases h with ⟨hB, hW, hzB, hzW, hBW⟩
  have hsub : ∀ k ∈ labels [V], k ∈ labels [W] := by
    intro k hk
    obtain ⟨d, hd, rfl⟩ := label_mem_word.mp hk
    apply label_mem_word.mpr
    exact ⟨d, hp.mem_iff.mpr (by simp [hd]), rfl⟩
  exact ⟨hB, (List.nodup_append.mp (hp.nodup_iff.mp hW)).2.1, hzB,
    fun hz ↦ hzW (hsub _ hz), fun k hk hm ↦ hBW k hk (hsub _ hm)⟩

private theorem ReductionReady.selected_fresh {B : List ReductionBlock} {z d : Dart} {W : Word}
    (h : ReductionReady B z W) (hd : d ∈ W) :
    d.1 ∉ labels [blocksWord B ++ [z]] := by
  have hmem : d.1 ∈ labels [W] := label_mem_word.mpr ⟨d, hd, rfl⟩
  rw [label_mem_append, blocks_label_mem]
  simp only [labels, occurrences, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
    Finset.mem_insert, Finset.notMem_empty, or_false, not_or]
  exact ⟨fun hB ↦ h.2.2.2.2 _ hB hmem, fun hz ↦ h.2.2.2.1 (hz ▸ hmem)⟩

private theorem unpaired_label_fresh (a : Dart) (L R : Word)
    (hnd : (L ++ a :: R).Nodup) (hu : inverse a ∉ L ++ a :: R) :
    a.1 ∉ labels [L, R] := by
  intro ha
  simp only [labels, occurrences, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.mem_toFinset, List.mem_map, List.mem_append] at ha
  obtain ⟨d, hd, he⟩ := ha
  have hnot : a ∉ L ∧ a ∉ R := by
    have hp := List.nodup_iff_count.mp hnd a
    simp [List.count_append] at hp
    constructor <;> intro hm <;> have hc := List.count_pos_iff.mpr hm <;> omega
  have hdne : d ≠ a := by
    intro heq
    subst d
    exact hd.elim hnot.1 hnot.2
  have hdinv : d = inverse a := by
    rcases a with ⟨a, s⟩
    rcases d with ⟨d, t⟩
    dsimp at he
    subst d
    cases s <;> cases t <;> simp_all [inverse]
  apply hu
  rw [← hdinv]
  simp only [List.mem_append, List.mem_cons]
  tauto

private theorem label_mem_cons (k : ℕ) (d : Dart) (W : Word) :
    k ∈ labels [d :: W] ↔ k = d.1 ∨ k ∈ labels [W] := by
  simp [labels, occurrences, eq_comm]

private theorem fresh_ready_word (k : ℕ) (B : List ReductionBlock) (z : Dart) (W : Word) :
    k ∉ labels [blocksWord B ++ z :: W] ↔
      k ∉ blocksLabels B ∧ k ≠ z.1 ∧ k ∉ labels [W] := by
  rw [label_mem_append, blocks_label_mem, label_mem_cons]
  tauto

private theorem ReductionReady.insert_fresh {B : List ReductionBlock} {z : Dart} {W : Word}
    (h : ReductionReady B z W) (d : Dart)
    (hd : d.1 ∉ labels [blocksWord B ++ z :: W]) : ReductionReady B z (d :: W) := by
  obtain ⟨hdB, hdz, hdW⟩ := (fresh_ready_word _ _ _ _).mp hd
  rcases h with ⟨hB, hW, hzB, hzW, hBW⟩
  refine ⟨hB, List.nodup_cons.mpr ⟨?_, hW⟩, hzB, ?_, ?_⟩
  · intro hm
    exact hdW (label_mem_word.mpr ⟨d, hm, rfl⟩)
  · rw [label_mem_cons]
    exact not_or.mpr ⟨Ne.symm hdz, hzW⟩
  · intro k hk hm
    rw [label_mem_cons] at hm
    rcases hm with rfl | hm
    · exact hdB hk
    · exact hBW k hk hm

private theorem ReductionReady.cons_block {B : List ReductionBlock} {z : Dart} {W : Word}
    (h : ReductionReady B z W) (q : ReductionBlock)
    (ha : q.a.1 ∉ labels [blocksWord B ++ z :: W])
    (hb : q.b.1 ∉ labels [blocksWord B ++ z :: W]) : ReductionReady (q :: B) z W := by
  obtain ⟨haB, haz, haW⟩ := (fresh_ready_word _ _ _ _).mp ha
  obtain ⟨hbB, hbz, hbW⟩ := (fresh_ready_word _ _ _ _).mp hb
  rcases h with ⟨hB, hW, hzB, hzW, hBW⟩
  refine ⟨?_, hW, ?_, hzW, ?_⟩
  · change (q.a.1 :: q.b.1 :: blocksLabels B).Nodup
    exact List.nodup_cons.mpr ⟨by simp [q.distinct, haB], List.nodup_cons.mpr ⟨hbB, hB⟩⟩
  · change z.1 ∉ q.a.1 :: q.b.1 :: blocksLabels B
    simp [Ne.symm haz, Ne.symm hbz, hzB]
  · intro k hk
    change k ∈ q.a.1 :: q.b.1 :: blocksLabels B at hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact haW
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hbW
    exact hBW k hk

private theorem ReductionReady.perm_blocks {B C : List ReductionBlock} {z : Dart} {W : Word}
    (h : ReductionReady B z W) (hp : B.Perm C) : ReductionReady C z W := by
  have he : (blocksLabels B).Perm (blocksLabels C) := hp.flatMap (fun _ _ ↦ List.Perm.refl _)
  rcases h with ⟨hB, hW, hzB, hzW, hBW⟩
  exact ⟨he.nodup_iff.mp hB, hW, fun hz ↦ hzB (he.mem_iff.mpr hz), hzW,
    fun k hk ↦ hBW k (he.mem_iff.mpr hk)⟩

private theorem ReductionReady.append_block {B : List ReductionBlock} {z : Dart} {W : Word}
    (h : ReductionReady B z W) (q : ReductionBlock)
    (ha : q.a.1 ∉ labels [blocksWord B ++ z :: W])
    (hb : q.b.1 ∉ labels [blocksWord B ++ z :: W]) : ReductionReady (B ++ [q]) z W := by
  exact (h.cons_block q ha hb).perm_blocks (List.perm_append_comm (l₁ := [q]) (l₂ := B))

private theorem OrderedBlocks.cons_handle {B : List ReductionBlock} (h : OrderedBlocks B)
    (q : ReductionBlock) (hq : q.isHandle = true) : OrderedBlocks (q :: B) := by
  exact List.pairwise_cons.mpr ⟨fun r hr hrt ↦ hq, h⟩

private theorem OrderedBlocks.append_loop {B : List ReductionBlock} (h : OrderedBlocks B)
    (q : ReductionBlock) (hq : q.isHandle = false) : OrderedBlocks (B ++ [q]) := by
  apply List.pairwise_append.mpr
  refine ⟨h, by simp, ?_⟩
  intro a ha b hb hbtrue
  have he : b = q := by simpa using hb
  subst b
  simp [hq] at hbtrue

private theorem fresh_append_context (k : ℕ) (A L R : Word) :
    k ∉ labels [A ++ L, R] ↔ k ∉ labels [A] ∧ k ∉ labels [L, R] := by
  simp [labels, occurrences, and_assoc]

private def ReductionProgress (B : List ReductionBlock) (z : Dart) (W : Word) : Prop :=
  ∃ (C : List ReductionBlock) (d : Dart) (V : Word), V.length < W.length ∧
    ReductionReady C d V ∧ OrderedBlocks C ∧
      PresentationEquivalent [blocksWord B ++ z :: W] [blocksWord C ++ d :: V]

private theorem reduction_last_side (B : List ReductionBlock) (z d : Dart)
    (h : ReductionReady B z [d]) (ho : OrderedBlocks B) : ReductionProgress B z [d] := by
  obtain ⟨c, hc⟩ := (labels [blocksWord B ++ z :: [d]]).exists_notMem
  obtain ⟨hcB, hcz, hcd⟩ := (fresh_ready_word _ _ _ _).mp hc
  have hcd' : c ≠ d.1 := by simpa [labels, occurrences] using hcd
  have hzB : z.1 ∉ labels [blocksWord B] := (blocks_label_mem B z.1).not.mpr h.2.2.1
  have hdB : d.1 ∉ labels [blocksWord B] := by
    rw [blocks_label_mem]
    intro hd
    exact h.2.2.2.2 d.1 hd (label_mem_word.mpr ⟨d, by simp, rfl⟩)
  have hzd : z.1 ≠ d.1 := by simpa [labels, occurrences] using h.2.2.2.1
  have hcB' : c ∉ labels [blocksWord B] := (blocks_label_mem B c).not.mpr hcB
  have he := contextual_boundary_contraction z d c (blocksWord B) [] hzd
    (by simpa [labels, occurrences] using hzB)
    (by simpa [labels, occurrences] using hdB)
    (by simpa [labels, occurrences] using hcB') hcz hcd'
  refine ⟨B, (c, true), [], by simp, ?_, ho, ?_⟩
  · exact ⟨h.1, by simp, hcB, by simp [labels, occurrences],
      fun _ _ ↦ by simp [labels, occurrences]⟩
  · simpa using he

private theorem reduction_spur (B : List ReductionBlock) (z a : Dart) (L R : Word)
    (h : ReductionReady B z (L ++ a :: inverse a :: R)) (ho : OrderedBlocks B) :
    ReductionProgress B z (L ++ a :: inverse a :: R) := by
  have hp : (L ++ a :: inverse a :: R).Perm ([a, inverse a] ++ (L ++ R)) := by
    apply List.perm_iff_count.mpr
    intro d
    simp only [List.count_append, List.count_cons, List.count_nil]
    omega
  have hres := h.residual hp
  have ha := paired_label_fresh a L [] R (by simpa using h.2.1)
  have ha' : a.1 ∉ labels [L, R] := by simpa [labels, occurrences] using ha
  have hap := h.selected_fresh (d := a) (by simp)
  have haf : a.1 ∉ labels [(blocksWord B ++ [z]) ++ L, R] :=
    (fresh_append_context _ _ _ _).mpr ⟨hap, ha'⟩
  have he := contextual_spur_cancellation a ((blocksWord B ++ [z]) ++ L) R (by simp) haf
  refine ⟨B, z, L ++ R, ?_, hres, ho, ?_⟩
  · simp only [List.length_append, List.length_cons]
    omega
  · simpa [List.append_assoc] using he

private theorem fresh_residual_word {B : List ReductionBlock} {z : Dart} {W V D : Word}
    (hp : W.Perm (D ++ V)) (k : ℕ)
    (hk : k ∉ labels [blocksWord B ++ z :: W]) :
    k ∉ labels [blocksWord B ++ z :: V] := by
  rw [fresh_ready_word] at hk ⊢
  refine ⟨hk.1, hk.2.1, ?_⟩
  intro hm
  obtain ⟨d, hd, he⟩ := label_mem_word.mp hm
  exact hk.2.2 (label_mem_word.mpr ⟨d, hp.mem_iff.mpr (by simp [hd]), he⟩)

private theorem reduction_boundary_pair (B : List ReductionBlock) (z a b : Dart) (L R : Word)
    (h : ReductionReady B z (L ++ a :: b :: R)) (ho : OrderedBlocks B)
    (hu : inverse a ∉ L ++ a :: b :: R) (hv : inverse b ∉ L ++ a :: b :: R) :
    ReductionProgress B z (L ++ a :: b :: R) := by
  have haAll := unpaired_label_fresh a L (b :: R) h.2.1 hu
  have hbAll := unpaired_label_fresh b (L ++ [a]) R
    (by simpa [List.append_assoc] using h.2.1) (by simpa [List.append_assoc] using hv)
  have ha : a.1 ≠ b.1 ∧ a.1 ∉ labels [L, R] := by
    simp [labels, occurrences] at haAll ⊢
    tauto
  have hb : b.1 ∉ labels [L, R] := by
    simp [labels, occurrences] at hbAll ⊢
    tauto
  have hap := h.selected_fresh (d := a) (by simp)
  have hbp := h.selected_fresh (d := b) (by simp)
  have haf : a.1 ∉ labels [(blocksWord B ++ [z]) ++ L, R] :=
    (fresh_append_context _ _ _ _).mpr ⟨hap, ha.2⟩
  have hbf : b.1 ∉ labels [(blocksWord B ++ [z]) ++ L, R] :=
    (fresh_append_context _ _ _ _).mpr ⟨hbp, hb⟩
  obtain ⟨c, hc⟩ := (labels [blocksWord B ++ z :: (L ++ a :: b :: R)]).exists_notMem
  have hcW := ((fresh_ready_word _ _ _ _).mp hc).2.2
  have hca : c ≠ a.1 := by
    intro he
    exact hcW (label_mem_word.mpr ⟨a, by simp, he.symm⟩)
  have hcb : c ≠ b.1 := by
    intro he
    exact hcW (label_mem_word.mpr ⟨b, by simp, he.symm⟩)
  have hp : (L ++ a :: b :: R).Perm ([a, b] ++ (L ++ R)) := by
    apply List.perm_iff_count.mpr
    intro d
    simp only [List.count_append, List.count_cons, List.count_nil]
    omega
  have hres := h.residual hp
  have hcf := fresh_residual_word hp c hc
  have hnew := hres.insert_fresh (c, true) hcf
  have hvp : ((c, true) :: (L ++ R)).Perm (L ++ (c, true) :: R) := by
    apply List.perm_iff_count.mpr
    intro d
    simp only [List.count_append, List.count_cons]
    omega
  have hready : ReductionReady B z (L ++ (c, true) :: R) :=
    hnew.residual (D := []) (by simpa using hvp)
  have he := contextual_boundary_contraction a b c ((blocksWord B ++ [z]) ++ L) R ha.1 haf hbf
    (by simpa [labels, occurrences, List.append_assoc] using hcf) hca hcb
  refine ⟨B, z, L ++ (c, true) :: R, ?_, hready, ho, ?_⟩
  · simp only [List.length_append, List.length_cons]
    omega
  · simpa [List.append_assoc] using he

private theorem reduction_loop (B : List ReductionBlock) (z a b : Dart) (L R : Word)
    (h : ReductionReady B z (L ++ a :: b :: inverse a :: R)) (ho : OrderedBlocks B)
    (hu : inverse b ∉ L ++ a :: b :: inverse a :: R) :
    ReductionProgress B z (L ++ a :: b :: inverse a :: R) := by
  have haAll := paired_label_fresh a L [b] R (by simpa using h.2.1)
  have hbAll := unpaired_label_fresh b (L ++ [a]) (inverse a :: R)
    (by simpa [List.append_assoc] using h.2.1) (by simpa [List.append_assoc] using hu)
  have ha : a.1 ≠ b.1 ∧ a.1 ∉ labels [L, R] := by
    simp [labels, occurrences] at haAll ⊢
    tauto
  have hb : b.1 ∉ labels [L, R] := by
    simp [labels, occurrences] at hbAll ⊢
    tauto
  let q : ReductionBlock := ⟨false, a, b, ha.1⟩
  have hap := h.selected_fresh (d := a) (by simp)
  have hbp := h.selected_fresh (d := b) (by simp)
  have hp : (L ++ a :: b :: inverse a :: R).Perm ([a, b, inverse a] ++ (L ++ R)) := by
    apply List.perm_iff_count.mpr
    intro d
    simp only [List.count_append, List.count_cons, List.count_nil]
    omega
  have hres := h.residual hp
  have hqa : q.a.1 ∉ labels [blocksWord B ++ z :: (L ++ R)] := by
    have hf : a.1 ∉ labels [(blocksWord B ++ [z]) ++ (L ++ R)] := by
      rw [label_mem_append]
      exact not_or.mpr ⟨hap, by simpa [labels, occurrences] using ha.2⟩
    simpa [q, List.append_assoc] using hf
  have hqb : q.b.1 ∉ labels [blocksWord B ++ z :: (L ++ R)] := by
    have hf : b.1 ∉ labels [(blocksWord B ++ [z]) ++ (L ++ R)] := by
      rw [label_mem_append]
      exact not_or.mpr ⟨hbp, by simpa [labels, occurrences] using hb⟩
    simpa [q, List.append_assoc] using hf
  have he := q.move_left_context (blocksWord B) (z :: L) R
    (by simpa [labels, occurrences, List.append_assoc] using hqa)
    (by simpa [labels, occurrences, List.append_assoc] using hqb)
  refine ⟨B ++ [q], z, L ++ R, ?_, hres.append_block q hqa hqb,
    ho.append_loop q rfl, ?_⟩
  · simp only [List.length_append, List.length_cons]
    omega
  · simpa [blocksWord, q, ReductionBlock.word, List.flatMap_append, List.append_assoc] using he

private theorem reduction_handle (B : List ReductionBlock) (z a b : Dart) (L U V X Y : Word)
    (h : ReductionReady B z (L ++ a :: (U ++ b :: (V ++ inverse a :: (X ++ inverse b :: Y)))))
    (ho : OrderedBlocks B) :
    ReductionProgress B z (L ++ a :: (U ++ b :: (V ++ inverse a :: (X ++ inverse b :: Y)))) := by
  have haAll := paired_label_fresh a L (U ++ b :: V) (X ++ inverse b :: Y)
    (by simpa [List.append_assoc] using h.2.1)
  have hbAll := paired_label_fresh b (L ++ a :: U) (V ++ inverse a :: X) Y
    (by simpa [List.append_assoc] using h.2.1)
  have ha : a.1 ≠ b.1 ∧ a.1 ∉ labels [L, U, V, X, Y] := by
    simp [labels, occurrences, inverse] at haAll ⊢
    tauto
  have hb : b.1 ∉ labels [L, U, V, X, Y] := by
    simp [labels, occurrences, inverse] at hbAll ⊢
    tauto
  have hap := h.selected_fresh (d := a) (by simp)
  have hbp := h.selected_fresh (d := b) (by simp)
  have haf : a.1 ∉ labels [blocksWord B ++ z :: L, U, V, X, Y] := by
    simpa [labels, occurrences, List.append_assoc, and_assoc] using And.intro hap ha.2
  have hbf : b.1 ∉ labels [blocksWord B ++ z :: L, U, V, X, Y] := by
    simpa [labels, occurrences, List.append_assoc, and_assoc] using And.intro hbp hb
  obtain ⟨q, hq, hqa, hqb, he⟩ := contextual_handle_extraction a b
    (blocksWord B ++ z :: L) U V X Y haf hbf ha.1
  have hp : (L ++ a :: (U ++ b :: (V ++ inverse a :: (X ++ inverse b :: Y)))).Perm
      ([a, b, inverse a, inverse b] ++ (L ++ X ++ V ++ U ++ Y)) := by
    apply List.perm_iff_count.mpr
    intro d
    simp only [List.count_append, List.count_cons, List.count_nil]
    omega
  have hres := h.residual hp
  have hf (k : ℕ) (hk : k ∉ labels [blocksWord B ++ z :: L, U, V, X, Y]) :
      k ∉ labels [blocksWord B ++ z :: (L ++ X ++ V ++ U ++ Y)] := by
    intro hm
    obtain ⟨d, hd, he⟩ := label_mem_word.mp hm
    apply hk
    simp only [labels, occurrences, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.mem_toFinset, List.mem_map]
    refine ⟨d, ?_, he⟩
    simp only [List.mem_append, List.mem_cons] at hd ⊢
    tauto
  have hqaf := hf q.a.1 hqa
  have hqbf := hf q.b.1 hqb
  refine ⟨q :: B, z, L ++ X ++ V ++ U ++ Y, ?_, hres.cons_block q hqaf hqbf,
    ho.cons_handle q hq, ?_⟩
  · simp only [List.length_append, List.length_cons]
    omega
  · simpa [blocksWord, List.append_assoc] using he

private theorem reduction_progress (B : List ReductionBlock) (z : Dart) (W : Word)
    (h : ReductionReady B z W) (ho : OrderedBlocks B) (hne : W ≠ []) :
    ReductionProgress B z W := by
  rcases word_reduction_case W h.2.1 with hlen | hs | hb | hl | hh
  · cases W with
    | nil => exact False.elim (hne rfl)
    | cons d W =>
      have hw : W = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen; omega)
      subst W
      exact reduction_last_side B z d h ho
  · obtain ⟨a, L, R, rfl⟩ := hs
    exact reduction_spur B z a L R h ho
  · obtain ⟨a, b, L, R, rfl, hu, hv⟩ := hb
    exact reduction_boundary_pair B z a b L R h ho hu hv
  · obtain ⟨a, b, L, R, rfl, hu⟩ := hl
    exact reduction_loop B z a b L R h ho hu
  · obtain ⟨a, b, L, U, V, X, Y, rfl⟩ := hh
    exact reduction_handle B z a b L U V X Y h ho

/-- Strong induction for the finite word reduction, retaining one unpaired
boundary side as an anchor. The innermost-pair case selection supplies one
of the four proper macros. Each removes at least one active side; completed
handles are prepended and completed boundary loops are appended. Fresh-label
and signed-occurrence invariants ensure every macro is applicable, and the
anchor prevents a spur cancellation from leaving an empty presentation. -/
private theorem anchored_word_normalization (B : List ReductionBlock) (z : Dart) (W : Word)
    (h : ReductionReady B z W) (ho : OrderedBlocks B) :
    ∃ (C : List ReductionBlock) (d : Dart), ReductionReady C d [] ∧ OrderedBlocks C ∧
      PresentationEquivalent [blocksWord B ++ z :: W] [blocksWord C ++ [d]] := by
  generalize hn : W.length = n
  induction n using Nat.strong_induction_on generalizing B z W with
  | h n ih =>
    by_cases hW : W = []
    · subst W
      exact ⟨B, z, h, ho, PresentationEquivalent.refl _⟩
    · obtain ⟨C, d, V, hlen, hC, hoC, he⟩ := reduction_progress B z W h ho hW
      obtain ⟨E, e, hE, hoE, he'⟩ := ih V.length (by omega) C d V hC hoC rfl
      exact ⟨E, e, hE, hoE, he.trans he'⟩

private theorem blocks_move_left (B : List ReductionBlock) (L R : Word)
    (hB : (blocksLabels B).Nodup)
    (hf : ∀ k ∈ blocksLabels B, k ∉ labels [L, R]) :
    PresentationEquivalent [L ++ blocksWord B ++ R] [blocksWord B ++ L ++ R] := by
  induction B generalizing L R with
  | nil => simpa [blocksWord] using PresentationEquivalent.refl [L ++ R]
  | cons q B ih =>
    change (q.a.1 :: q.b.1 :: blocksLabels B).Nodup at hB
    obtain ⟨hqa, hB⟩ := List.nodup_cons.mp hB
    obtain ⟨hqb, hB⟩ := List.nodup_cons.mp hB
    have hqaB : q.a.1 ∉ blocksLabels B := fun hk ↦ hqa (List.mem_cons_of_mem _ hk)
    have hqam : q.a.1 ∉ labels [L, blocksWord B ++ R] := by
      intro hm
      simp only [labels, occurrences, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.mem_toFinset, List.mem_map, List.mem_append] at hm
      obtain ⟨d, hd, he⟩ := hm
      rcases hd with hd | hd | hd
      · exact hf q.a.1 (by change _ ∈ q.a.1 :: q.b.1 :: blocksLabels B; simp) (by
        simp only [labels, occurrences, List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_toFinset, List.mem_map]
        exact ⟨d, List.mem_append_left _ hd, he⟩)
      · exact hqaB ((blocks_label_mem B _).mp (label_mem_word.mpr ⟨d, hd, he⟩))
      · exact hf q.a.1 (by change _ ∈ q.a.1 :: q.b.1 :: blocksLabels B; simp) (by
        simp only [labels, occurrences, List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_toFinset, List.mem_map]
        exact ⟨d, List.mem_append_right _ hd, he⟩)
    have hqbm : q.b.1 ∉ labels [L, blocksWord B ++ R] := by
      intro hm
      simp only [labels, occurrences, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.mem_toFinset, List.mem_map, List.mem_append] at hm
      obtain ⟨d, hd, he⟩ := hm
      rcases hd with hd | hd | hd
      · exact hf q.b.1 (by change _ ∈ q.a.1 :: q.b.1 :: blocksLabels B; simp) (by
        simp only [labels, occurrences, List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_toFinset, List.mem_map]
        exact ⟨d, List.mem_append_left _ hd, he⟩)
      · exact hqb ((blocks_label_mem B _).mp (label_mem_word.mpr ⟨d, hd, he⟩))
      · exact hf q.b.1 (by change _ ∈ q.a.1 :: q.b.1 :: blocksLabels B; simp) (by
        simp only [labels, occurrences, List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_toFinset, List.mem_map]
        exact ⟨d, List.mem_append_right _ hd, he⟩)
    have hfirst := q.move_left L (blocksWord B ++ R) hqam hqbm
    have hrest := ih L (R ++ q.word) hB (by
      intro k hk hm
      have hknqa : k ≠ q.a.1 := by intro he; subst k; exact hqaB hk
      have hknqb : k ≠ q.b.1 := by intro he; subst k; exact hqb hk
      have hno : k ∉ labels [q.word] := by rw [q.label_mem_word]; tauto
      simp only [labels, occurrences, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.mem_toFinset, List.mem_map, List.mem_append] at hm
      obtain ⟨d, hd, he⟩ := hm
      rcases hd with hd | hd | hd
      · exact hf k (by change _ ∈ q.a.1 :: q.b.1 :: blocksLabels B; simp [hk]) (by
        simp only [labels, occurrences, List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_toFinset, List.mem_map]
        exact ⟨d, List.mem_append_left _ hd, he⟩)
      · exact hf k (by change _ ∈ q.a.1 :: q.b.1 :: blocksLabels B; simp [hk]) (by
        simp only [labels, occurrences, List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_toFinset, List.mem_map]
        exact ⟨d, List.mem_append_right _ hd, he⟩)
      · exact hno (label_mem_word.mpr ⟨d, hd, he⟩))
    have r1 : PresentationEquivalent [q.word ++ L ++ (blocksWord B ++ R)]
        [L ++ blocksWord B ++ (R ++ q.word)] := by
      apply singleton_rotation
      simpa [List.append_assoc] using (List.isRotated_append
        (l := q.word) (l' := L ++ blocksWord B ++ R))
    have r2 : PresentationEquivalent [blocksWord B ++ L ++ (R ++ q.word)]
        [q.word ++ blocksWord B ++ L ++ R] := by
      apply singleton_rotation
      simpa [List.append_assoc] using (List.isRotated_append
        (l := blocksWord B ++ L ++ R) (l' := q.word))
    apply PresentationEquivalent.trans (Q := [q.word ++ L ++ (blocksWord B ++ R)])
    · simpa [blocksWord, List.append_assoc] using hfirst
    simpa [blocksWord, List.append_assoc] using r1.trans (hrest.trans r2)

private theorem close_boundary_anchor (B : List ReductionBlock) (z : Dart)
    (h : ReductionReady B z []) (ho : OrderedBlocks B) :
    ∃ C : List ReductionBlock, (blocksLabels C).Nodup ∧ OrderedBlocks C ∧
      (∃ q ∈ C, q.isHandle = false) ∧
      PresentationEquivalent [blocksWord B ++ [z]] [blocksWord C] := by
  obtain ⟨c, hc⟩ := (insert z.1 (blocksLabels B).toFinset).exists_notMem
  simp only [Finset.mem_insert, List.mem_toFinset, not_or] at hc
  let q : ReductionBlock := ⟨false, (c, true), z, hc.1⟩
  have hcf : c ∉ labels [blocksWord B ++ [z]] := by
    rw [label_mem_append, blocks_label_mem]
    simp [labels, occurrences, hc]
  have hspur := signed_spur_cancellation (c, false) (blocksWord B ++ [z]) (by simp) hcf
  have hmove := blocks_move_left B [(c, true)] [z, (c, false)] h.1 (by
    intro k hk
    have hkc : k ≠ c := by intro he; subst k; exact hc.2 hk
    have hkz : k ≠ z.1 := by intro he; subst k; exact h.2.2.1 hk
    simp [labels, occurrences, hkc, hkz])
  have r1 : PresentationEquivalent [(c, false) :: inverse (c, false) :: (blocksWord B ++ [z])]
      [(c, true) :: (blocksWord B ++ [z, (c, false)])] := by
    apply singleton_rotation
    simpa [inverse, List.append_assoc] using
      (List.isRotated_append (l := [(c, false)]) (l' := (c, true) :: (blocksWord B ++ [z])))
  have hqaf : q.a.1 ∉ labels [blocksWord B ++ z :: []] := hcf
  have hqbf : q.b.1 ∉ labels [blocksWord B] := (blocks_label_mem B z.1).not.mpr h.2.2.1
  refine ⟨B ++ [q], ?_, ho.append_loop q rfl, ⟨q, by simp, rfl⟩, ?_⟩
  · have hcnd : (c :: z.1 :: blocksLabels B).Nodup :=
      List.nodup_cons.mpr ⟨by simp [hc], List.nodup_cons.mpr ⟨h.2.2.1, h.1⟩⟩
    have hp : (blocksLabels (q :: B)).Perm (blocksLabels (B ++ [q])) :=
      (List.perm_append_comm (l₁ := [q]) (l₂ := B)).flatMap (fun _ _ ↦ List.Perm.refl _)
    exact hp.nodup_iff.mp hcnd
  · apply hspur.symm.trans
    apply r1.trans
    simpa [blocksWord, q, ReductionBlock.word, inverse, List.append_assoc] using hmove

private def signedRename (e : ℕ ≃ ℕ) (flip : ℕ → Bool) (d : Dart) : Dart :=
  (e d.1, if flip d.1 then !d.2 else d.2)

private theorem signedRename_inverse (e : ℕ ≃ ℕ) (flip : ℕ → Bool) (d : Dart) :
    signedRename e flip (inverse d) = inverse (signedRename e flip d) := by
  rcases d with ⟨d, s⟩
  simp only [signedRename, inverse]
  by_cases hf : flip d = true <;> simp [hf]

private def blockDarts (B : List ReductionBlock) : Word := B.flatMap fun q ↦ [q.a, q.b]

private theorem blockDarts_labels (B : List ReductionBlock) :
    (blockDarts B).map Prod.fst = blocksLabels B := by
  induction B with
  | nil => rfl
  | cons q B ih => simpa only [blockDarts, blocksLabels, List.flatMap_cons, List.map_append,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append] using congrArg (q.a.1 :: q.b.1 :: ·) ih

private theorem blockDarts_length (B : List ReductionBlock) : (blockDarts B).length = 2 * B.length := by
  induction B with
  | nil => rfl
  | cons q B ih => simp only [blockDarts, List.flatMap_cons, List.length_append,
      List.length_cons, List.length_nil] at ih ⊢; omega

private theorem signed_list_enumeration (D : Word) (hD : (D.map Prod.fst).Nodup) :
    ∃ (e : ℕ ≃ ℕ) (flip : ℕ → Bool), ∀ i : Fin D.length,
      signedRename e flip (D.get i) = (i.val, true) := by
  let f : Fin D.length → ℕ := fun i ↦ (D.get i).1
  have hf : Function.Injective f := by
    intro i j he
    have he' : (D.map Prod.fst).get ⟨i.val, by simp⟩ =
        (D.map Prod.fst).get ⟨j.val, by simp⟩ := by simpa [f] using he
    have h := hD.injective_get he'
    exact Fin.ext (congrArg (fun q : Fin (D.map Prod.fst).length ↦ q.val) h)
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair f Fin.val hf Fin.val_injective
  let flip : ℕ → Bool := Function.extend f (fun i ↦ !(D.get i).2) (fun _ ↦ false)
  refine ⟨e, flip, ?_⟩
  intro i
  have hflip : flip (D.get i).1 = !(D.get i).2 := hf.extend_apply _ _ i
  change (e (f i), if flip (D.get i).1 then !(D.get i).2 else (D.get i).2) = _
  rw [he i, hflip]
  cases (D.get i).2 <;> rfl

private def canonicalBlocks (k : ℕ) : List ReductionBlock → Word
  | [] => []
  | q :: B =>
      (if q.isHandle then [(k, true), (k+1, true), (k, false), (k+1, false)]
       else [(k, true), (k+1, true), (k, false)]) ++ canonicalBlocks (k+2) B

private theorem canonicalBlocks_rename (B : List ReductionBlock) (k : ℕ) (e : ℕ ≃ ℕ)
    (flip : ℕ → Bool)
    (h : ∀ i : Fin (blockDarts B).length,
      signedRename e flip ((blockDarts B).get i) = (k + i.val, true)) :
    (blocksWord B).map (signedRename e flip) = canonicalBlocks k B := by
  induction B generalizing k with
  | nil => rfl
  | cons q B ih =>
    have ha := h ⟨0, by simp [blockDarts]⟩
    have hb := h ⟨1, by simp [blockDarts]⟩
    change signedRename e flip q.a = (k + 0, true) at ha
    change signedRename e flip q.b = (k + 1, true) at hb
    simp only [Nat.add_zero] at ha
    have ht : ∀ i : Fin (blockDarts B).length,
        signedRename e flip ((blockDarts B).get i) = (k + 2 + i.val, true) := by
      intro i
      have hi := h ⟨i.val + 2, by simp only [blockDarts, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]; have := i.isLt; change i.val < (B.flatMap fun q ↦ [q.a, q.b]).length at this; omega⟩
      simp only [List.get_eq_getElem]
      simpa [blockDarts, List.get_eq_getElem, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
    change (q.word ++ blocksWord B).map (signedRename e flip) = _
    rw [List.map_append, ih (k+2) ht]
    simp only [canonicalBlocks, ReductionBlock.word]
    have hai : signedRename e flip (inverse q.a) = (k, false) := by rw [signedRename_inverse, ha]; rfl
    have hbi : signedRename e flip (inverse q.b) = (k+1, false) := by rw [signedRename_inverse, hb]; rfl
    cases hq : q.isHandle <;> simp [ha, hb, hai, hbi]

private theorem blocks_have_canonical_renaming (B : List ReductionBlock)
    (hB : (blocksLabels B).Nodup) :
    ∃ (e : ℕ ≃ ℕ) (flip : ℕ → Bool),
      (blocksWord B).map (signedRename e flip) = canonicalBlocks 0 B := by
  obtain ⟨e, flip, he⟩ := signed_list_enumeration (blockDarts B) (by rwa [blockDarts_labels])
  exact ⟨e, flip, canonicalBlocks_rename B 0 e flip (by simpa using he)⟩

private def shiftedNormalWord (k g b : ℕ) : Word :=
  ((List.range g).flatMap fun i ↦
    [(k+2*i, true), (k+2*i+1, true), (k+2*i, false), (k+2*i+1, false)]) ++
  ((List.range b).flatMap fun j ↦
    [(k+2*g+2*j, true), (k+2*g+2*j+1, true), (k+2*g+2*j, false)])

private theorem shiftedNormalWord_zero (g b : ℕ) : shiftedNormalWord 0 g b = normalWord g b := by
  simp [shiftedNormalWord, normalWord]

private theorem shiftedNormalWord_handle (k g b : ℕ) :
    shiftedNormalWord k (g+1) b =
      [(k, true), (k+1, true), (k, false), (k+1, false)] ++ shiftedNormalWord (k+2) g b := by
  simp only [shiftedNormalWord, List.range_succ_eq_map, List.flatMap_cons,
    List.flatMap_map]
  simp only [Nat.mul_zero, Nat.add_zero, List.append_assoc]
  simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem shiftedNormalWord_loop (k b : ℕ) :
    shiftedNormalWord k 0 (b+1) =
      [(k, true), (k+1, true), (k, false)] ++ shiftedNormalWord (k+2) 0 b := by
  simp only [shiftedNormalWord, List.range_zero, List.flatMap_nil, List.nil_append,
    List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  simp only [Nat.mul_zero, Nat.add_zero]
  simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem canonicalBlocks_all_loops (B : List ReductionBlock) (k : ℕ)
    (h : ∀ q ∈ B, q.isHandle = false) : canonicalBlocks k B = shiftedNormalWord k 0 B.length := by
  induction B generalizing k with
  | nil => simp [canonicalBlocks, shiftedNormalWord]
  | cons q B ih =>
    simp only [canonicalBlocks, h q (by simp), Bool.false_eq_true, ↓reduceIte, List.length_cons]
    rw [ih _ (fun q hq ↦ h q (by simp [hq])), shiftedNormalWord_loop]

private theorem ordered_canonicalBlocks (B : List ReductionBlock) (k : ℕ) (ho : OrderedBlocks B) :
    ∃ g b, canonicalBlocks k B = shiftedNormalWord k g b ∧
      (0 < b ↔ ∃ q ∈ B, q.isHandle = false) := by
  induction B generalizing k with
  | nil => exact ⟨0, 0, rfl, by simp⟩
  | cons q B ih =>
    obtain ⟨hfirst, htail⟩ := List.pairwise_cons.mp ho
    cases hq : q.isHandle
    · have hloops : ∀ r ∈ q :: B, r.isHandle = false := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hq
        · cases hrh : r.isHandle
          · rfl
          · have := hfirst r hr hrh
            simp [hq] at this
      refine ⟨0, (q :: B).length, canonicalBlocks_all_loops _ _ hloops, ?_⟩
      simp only [List.length_cons, Nat.succ_pos, true_iff]
      exact ⟨q, by simp, hq⟩
    · obtain ⟨g, b, he, hb⟩ := ih (k+2) htail
      refine ⟨g+1, b, ?_, ?_⟩
      · simp only [canonicalBlocks, hq, ↓reduceIte]
        rw [he, shiftedNormalWord_handle]
      · simpa [hq] using hb

private theorem canonical_blocks_normal_form (B : List ReductionBlock)
    (hB : (blocksLabels B).Nodup) (ho : OrderedBlocks B)
    (hloop : ∃ q ∈ B, q.isHandle = false) :
    ∃ g b, 0 < b ∧ ∃ (e : ℕ ≃ ℕ) (flip : ℕ → Bool),
      (blocksWord B).map (signedRename e flip) = normalWord g b := by
  obtain ⟨g, b, he, hb⟩ := ordered_canonicalBlocks B 0 ho
  obtain ⟨e, flip, hrename⟩ := blocks_have_canonical_renaming B hB
  refine ⟨g, b, hb.mpr hloop, e, flip, ?_⟩
  rw [hrename, he, shiftedNormalWord_zero]

/-- Finite proper normalization of any coherently oriented polygon with an
unpaired boundary label. Source: Gallier–Xu Lemma 6.1 Steps 1, 2, 4–6,
pp.92–95. Retain an unpaired anchor, apply the strictly decreasing residual
word induction, create its final boundary-loop block by proper spur insertion,
and label the ordered distinct handle and loop sides consecutively. The
finite used-label injection extends to a permutation of natural labels. -/
theorem oriented_word_normalization (W : Word) (ho : Oriented [W])
    (hboundary : ∃ z ∈ W, inverse z ∉ W) :
    ∃ g b, 0 < b ∧ ∃ Q : Word, PresentationEquivalent [W] [Q] ∧
      ∃ (e : ℕ ≃ ℕ) (flip : ℕ → Bool),
        Q.map (fun d ↦ (e d.1, if flip d.1 then !d.2 else d.2)) = normalWord g b := by
  obtain ⟨z, hz, hzi⟩ := hboundary
  obtain ⟨L, R, hW, _⟩ := List.eq_append_cons_of_mem hz
  have hnd : W.Nodup := by simpa [occurrences] using (oriented_iff_nodup [W]).mp ho |>.2
  have hf := unpaired_label_fresh z L R (hW ▸ hnd) (hW ▸ hzi)
  have hp : W.Perm (z :: (R ++ L)) := by
    rw [hW]
    have hr : List.IsRotated (L ++ z :: R) (z :: (R ++ L)) :=
      List.isRotated_append (l := L) (l' := z :: R)
    exact hr.perm
  have hready : ReductionReady [] z (R ++ L) := by
    refine ⟨by simp [blocksLabels], (List.nodup_cons.mp (hp.nodup_iff.mp hnd)).2,
      by simp [blocksLabels], ?_, by simp [blocksLabels]⟩
    simpa [labels, occurrences, List.mem_map, List.mem_append, or_comm] using hf
  obtain ⟨B, d, hB, hoB, he⟩ := anchored_word_normalization [] z (R ++ L) hready (by simp [OrderedBlocks])
  obtain ⟨C, hC, hoC, hloop, he'⟩ := close_boundary_anchor B d hB hoB
  obtain ⟨g, b, hb, e, flip, hword⟩ := canonical_blocks_normal_form C hC hoC hloop
  refine ⟨g, b, hb, blocksWord C, ?_, e, flip, hword⟩
  have hr : PresentationEquivalent [W] [z :: (R ++ L)] := by
    rw [hW]
    apply singleton_rotation
    exact List.isRotated_append (l := L) (l' := z :: R)
  apply hr.trans
  apply PresentationEquivalent.trans (Q := [blocksWord B ++ [d]])
  · simpa [blocksWord] using he
  exact he'

private theorem edgeLabel_endpoint_pair {N : ℕ} {a b u v : Fin N}
    (hab : a ≠ b) (huv : u ≠ v) (h : edgeLabel a b = edgeLabel u v) :
    (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  have ha := edgeLabel_endpoint h
  have hb := edgeLabel_endpoint (edgeLabel_comm a b ▸ h)
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

private theorem triangle_side_label_injective {N : ℕ} {K : AbstractSimplicialComplex (Fin N)}
    (s : Triangle K) (o : Fin 3 ≃ ↥s.val) :
    Function.Injective (fun i : Fin 3 ↦ edgeLabel (o i).val (o (finRotate 3 i)).val) := by
  intro i j he
  have hne (k : Fin 3) : (o k).val ≠ (o (finRotate 3 k)).val := by
    intro h
    have hk := o.injective (Subtype.ext h)
    have hn : ∀ k : Fin 3, k ≠ finRotate 3 k := by decide
    exact hn k hk
  rcases edgeLabel_endpoint_pair (hne i) (hne j) he with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · exact o.injective (Subtype.ext hi)
  · have hi' := o.injective (Subtype.ext hi)
    have hj' := o.injective (Subtype.ext hj)
    have hn : ∀ i j : Fin 3, i = finRotate 3 j → finRotate 3 i = j → False := by decide
    exact False.elim (hn i j hi' hj')

private theorem triangle_label_unique {N : ℕ} {K : AbstractSimplicialComplex (Fin N)}
    (s : Triangle K) (o : Fin 3 ≃ ↥s.val) {a b : Dart}
    (ha : a ∈ triangleWord s o) (hb : b ∈ triangleWord s o) (he : a.1 = b.1) : a = b := by
  simp only [triangleWord, List.mem_map] at ha hb
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  have hij := triangle_side_label_injective s o he
  rw [hij]

private theorem occurrence_triangle {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) {d : Dart}
    (hd : d ∈ occurrences (trianglePresentation K o)) :
    ∃ s : Triangle K, d ∈ triangleWord s (o s) := by
  simp only [occurrences, List.mem_flatten, trianglePresentation, List.mem_map] at hd
  obtain ⟨w, ⟨s, hs, rfl⟩, hd⟩ := hd
  exact ⟨_, hd⟩

private theorem triangle_label_contains_edge {N : ℕ} {K : AbstractSimplicialComplex (Fin N)}
    (s : Triangle K) (o : Fin 3 ≃ ↥s.val) {d : Dart} (hd : d ∈ triangleWord s o)
    {u v : Fin N} (huv : u ≠ v) (he : d.1 = edgeLabel u v) :
    ({u, v} : Finset (Fin N)) ⊆ s.val := by
  simp only [triangleWord, List.mem_map] at hd
  obtain ⟨i, hi, rfl⟩ := hd
  have hn : (o i).val ≠ (o (finRotate 3 i)).val := by
    intro h
    have heq := o.injective (Subtype.ext h)
    have hh : ∀ i : Fin 3, i ≠ finRotate 3 i := by decide
    exact hh i heq
  have hpair := edgeLabel_endpoint_pair hn huv he
  rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨ha ▸ (o i).property, hb ▸ (o (finRotate 3 i)).property⟩
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hb ▸ (o (finRotate 3 i)).property, ha ▸ (o i).property⟩

/-- An original boundary edge supplies an unpaired signed occurrence in
the original triangle presentation. Source: Gallier–Xu Definition 6.1,
pp.79–81. Its incidence is one, hence exactly one original triangle contains
both endpoints. That triangle has exactly one side with the given unoriented
label. Any opposite occurrence would be another side of that same triangle,
contradicting the injectivity of its three side labels. -/
theorem boundary_edge_unpaired_occurrence {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    {u v : Fin N} (h : boundaryEdge K u v) :
    ∃ d ∈ occurrences (trianglePresentation K o), d.1 = edgeLabel u v ∧
      inverse d ∉ occurrences (trianglePresentation K o) := by
  obtain ⟨huv, hedge, hinc⟩ := h
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hinc
  have htm : t ∈ (simplices K 2).filter (fun t ↦ ({u, v} : Finset (Fin N)) ⊆ t) := by rw [ht]; simp
  obtain ⟨htri, hsub⟩ := Finset.mem_filter.mp htm
  let s : Triangle K := ⟨t, by simpa [simplices] using htri⟩
  obtain ⟨i, hi⟩ := triangle_pair_side s (o s) (hsub (by simp)) (hsub (by simp)) huv
  let d := (triangleWord s (o s)).get i
  have hd : d ∈ occurrences (trianglePresentation K o) := by
    obtain ⟨f, hf⟩ := triangle_word_occurs K o s
    apply List.mem_flatten.mpr
    refine ⟨_, List.get_mem _ f, ?_⟩
    rw [← hf]
    exact List.get_mem _ i
  refine ⟨d, hd, hi, ?_⟩
  intro hdi
  obtain ⟨s', hs'⟩ := occurrence_triangle K o hdi
  have hsub' := triangle_label_contains_edge s' (o s') hs' huv (by simpa [inverse, d] using hi)
  have hsm : s'.val ∈ (simplices K 2).filter (fun t ↦ ({u, v} : Finset (Fin N)) ⊆ t) := by
    exact Finset.mem_filter.mpr ⟨by simpa [simplices] using s'.property, hsub'⟩
  rw [ht, Finset.mem_singleton] at hsm
  have heq : s' = s := Subtype.ext hsm
  subst s'
  have hdEq := triangle_label_unique s (o s) hs' (List.get_mem _ i) (by rfl)
  exact inverse_ne_self d hdEq

/-- The supplied nonempty family of boundary cycles contains an original
boundary edge, hence an unpaired occurrence of the original presentation.
Only the cycle's first successor edge is needed for this existence statement. -/
theorem boundary_cycles_unpaired {N b : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (hb : 1 ≤ b)
    (B : Fin b → List (Fin N)) (hB : BoundaryCycles K B)
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) :
    ∃ d, UnpairedDart (trianglePresentation K o) d := by
  let j : Fin b := ⟨0, by omega⟩
  let i : Fin (B j).length := ⟨0, by have := (hB.1 j).2; omega⟩
  have hcycle : cycleEdge (B j) ((B j).get i) ((B j).get (finRotate (B j).length i)) :=
    ⟨i, Or.inl ⟨rfl, rfl⟩⟩
  have hedge := (hB.2.2 _ _).mpr ⟨j, hcycle⟩
  obtain ⟨d, hd, hl, hdi⟩ := boundary_edge_unpaired_occurrence K o hedge
  exact ⟨d, hd, hdi⟩

/-- The original connected coherently oriented surface presentation admits
a proper realized normal form with some positive number of boundary loops.
Source: Gallier–Xu Lemma 6.1, pp.92–95. Merge the original triangles while
retaining every unpaired occurrence. A supplied boundary cycle guarantees
one such occurrence, so the finite anchored polygon normalization applies.
The identification of the resulting loop count with the given family of
boundary cycles is the separate boundary-transport argument. -/
theorem triangle_presentation_normal_form {N b : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (hb : 1 ≤ b)
    (hconnected : IsConnected (carrier K)) (B : Fin b → List (Fin N))
    (hboundary : BoundaryCycles K B)
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (horiented : Oriented (trianglePresentation K o))
    (H₀ : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o)) :
    ∃ g b', 0 < b' ∧ ∃ Q : Word,
      PresentationEquivalent (trianglePresentation K o) [Q] ∧
      ∃ (e : ℕ ≃ ℕ) (flip : ℕ → Bool),
        Q.map (fun d ↦ (e d.1, if flip d.1 then !d.2 else d.2)) = normalWord g b' := by
  obtain ⟨W, hW, hoW, hlen, hboundaryW⟩ := triangle_presentation_one_face K hconnected o horiented H₀
  obtain ⟨d, hd⟩ := boundary_cycles_unpaired K hb B hboundary o
  have hdW := hboundaryW d hd
  obtain ⟨g, b', hb', Q, hQ, e, flip, he⟩ := oriented_word_normalization W hoW
    ⟨d, by simpa [UnpairedDart, occurrences] using hdW⟩
  exact ⟨g, b', hb', Q, hW.trans hQ, e, flip, he⟩

/-- Number of occurrences of an unoriented label in the finite presentation. -/
private def labelMultiplicity (P : Presentation) (a : ℕ) : ℕ :=
  ((occurrences P).map Prod.fst).count a

private theorem normal_boundary_block_count (g n j : ℕ) :
    ((List.range n).flatMap (fun i => [(2*g+2*i,true),(2*g+2*i+1,true),(2*g+2*i,false)]) |>.map Prod.fst).count (2*g+2*j+1) = if j < n then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.map_append, List.count_append, ih]
    have hne : 2*g+2*j+1 ≠ 2*g+2*n := by omega
    have he : (2*g+2*j+1 = 2*g+2*n+1) ↔ j = n := by omega
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_cons, List.map_nil, List.count_cons, List.count_nil, beq_iff_eq]
    simp only [Nat.zero_add]
    split_ifs <;> omega

private theorem normalWord_boundary_label_count {g b j : ℕ} (hj : j < b) :
    labelMultiplicity [normalWord g b] (2 * g + 2 * j + 1) = 1 := by
  have hleft : ((List.range g).flatMap (fun i => [(2*i,true),(2*i+1,true),(2*i,false),(2*i+1,false)]) |>.map Prod.fst).count (2*g+2*j+1) = 0 := by
    apply List.count_eq_zero.mpr
    intro hx
    obtain ⟨d, hd, he⟩ := List.mem_map.mp hx
    obtain ⟨i, hi, hd⟩ := List.mem_flatMap.mp hd
    have hi' := List.mem_range.mp hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> dsimp at he <;> omega
  simp only [labelMultiplicity, occurrences, List.flatten_cons, List.flatten_nil,
    List.append_nil, normalWord, List.map_append, List.count_append, hleft,
    normal_boundary_block_count, ite_eq_left hj, Nat.zero_add] 

private theorem normal_handle_label_count (g a : ℕ) :
    (((List.range g).flatMap (fun i ↦ [(2*i,true),(2*i+1,true),(2*i,false),(2*i+1,false)])).map Prod.fst).count a =
      if a < 2*g then 2 else 0 := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [List.range_succ, List.flatMap_append, List.map_append, List.count_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_cons, List.map_nil, List.count_cons, List.count_nil, beq_iff_eq]
    split_ifs <;> omega

private theorem normal_loop_label_count (g b a : ℕ) :
    (((List.range b).flatMap (fun j ↦ [(2*g+2*j,true),(2*g+2*j+1,true),(2*g+2*j,false)])).map Prod.fst).count a =
      if 2*g ≤ a ∧ a < 2*g+2*b then if a % 2 = 0 then 2 else 1 else 0 := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [List.range_succ, List.flatMap_append, List.map_append, List.count_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_cons, List.map_nil, List.count_cons, List.count_nil, beq_iff_eq]
    split_ifs <;> omega

private theorem normal_label_multiplicity (g b a : ℕ) :
    labelMultiplicity [normalWord g b] a =
      if a < 2*g then 2 else if a < 2*g+2*b then if a % 2 = 0 then 2 else 1 else 0 := by
  simp only [labelMultiplicity, occurrences, List.flatten_cons, List.flatten_nil,
    List.append_nil, normalWord, List.map_append, List.count_append,
    normal_handle_label_count, normal_loop_label_count]
  split_ifs <;> omega

private theorem normal_boundary_labels (g b a : ℕ) :
    labelMultiplicity [normalWord g b] a = 1 ↔ ∃ j : Fin b, a = 2*g+2*j.val+1 := by
  rw [normal_label_multiplicity]
  constructor
  · intro h
    have hge : 2*g ≤ a := by split_ifs at h <;> omega
    have hlt : a < 2*g+2*b := by split_ifs at h <;> omega
    have hodd : a % 2 = 1 := by split_ifs at h <;> omega
    refine ⟨⟨(a-2*g)/2, by omega⟩, ?_⟩
    dsimp
    omega
  · rintro ⟨j, rfl⟩
    have := j.isLt
    split_ifs <;> omega

/-- The boundary trace is the union of the images of labels occurring once.
Gallier–Xu Definition 6.1, pp.79–81. This is defined from the original
edge-parameter quotient, without any assumed surface classification. -/
private def boundaryImage (P : Presentation) : Set (Realization P) :=
  {x | ∃ a, labelMultiplicity P a = 1 ∧ x ∈ edgeImage P a}

private theorem labelMultiplicity_pos (P : Presentation) (a : ℕ) :
    0 < labelMultiplicity P a ↔ a ∈ labels P := by
  simp [labelMultiplicity, labels, List.count_pos_iff]

private theorem labelMultiplicity_zero (P : Presentation) (a : ℕ) :
    labelMultiplicity P a = 0 ↔ a ∉ labels P := by
  simpa only [Nat.not_lt, Nat.le_zero_eq] using not_congr (labelMultiplicity_pos P a)

private theorem label_side_exists {P : Presentation} {a : ℕ} (ha : a ∈ labels P) :
    ∃ f : Fin P.length, ∃ i : Fin (P.get f).length, ((P.get f).get i).1 = a := by
  simp only [labels, List.mem_toFinset, List.mem_map] at ha
  obtain ⟨d, hd, he⟩ := ha
  obtain ⟨w, hw, hdw⟩ := List.mem_flatten.mp hd
  obtain ⟨f, hf⟩ := List.mem_iff_get.mp hw
  subst w
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hdw
  exact ⟨f, i, hi ▸ he⟩

private def sideCurve (P : Presentation) (f : Fin P.length) (i : Fin (P.get f).length)
    (t : Icc (0 : ℝ) 1) : Realization P := project P (f, wordPoint (P.get f) i t)

private theorem sideCurve_mem (P : Presentation) (f : Fin P.length) (i : Fin (P.get f).length)
    (t : Icc (0 : ℝ) 1) : sideCurve P f i t ∈ edgeImage P ((P.get f).get i).1 := by
  refine ⟨(f, wordPoint (P.get f) i t), i, t.val, t.property, rfl, ?_, rfl⟩
  rfl

private theorem edgeImage_range (P : Presentation) (f : Fin P.length) (i : Fin (P.get f).length) :
    edgeImage P ((P.get f).get i).1 = Set.range (sideCurve P f i) := by
  ext x
  constructor
  · rintro ⟨y, j, t, ht, hl, hy, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    apply Quotient.sound
    apply Relation.EqvGen.rel
    exact ⟨i, j, t, ht, hl.symm, rfl, hy⟩
  · rintro ⟨t, rfl⟩
    exact sideCurve_mem P f i t

private theorem continuous_sideCurve (P : Presentation) (f : Fin P.length)
    (i : Fin (P.get f).length) : Continuous (sideCurve P f i) := by
  apply Continuous.comp continuous_quotient_mk'
  apply continuous_const.prodMk
  apply Continuous.subtype_mk
  unfold dartParameter
  split_ifs <;> fun_prop

private theorem edgeImage_compact (P : Presentation) (a : ℕ) : IsCompact (edgeImage P a) := by
  by_cases ha : a ∈ labels P
  · obtain ⟨f, i, rfl⟩ := label_side_exists ha
    rw [edgeImage_range]
    exact isCompact_range (continuous_sideCurve P f i)
  · have he : edgeImage P a = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨y, i, t, ht, he, hy, hq⟩
      apply ha
      simp only [labels, List.mem_toFinset, List.mem_map]
      exact ⟨_, List.mem_flatten.mpr ⟨_, List.get_mem _ y.1, List.get_mem _ i⟩, he⟩
    rw [he]
    exact isCompact_empty

private theorem edgeImage_connected {P : Presentation} {a : ℕ} (ha : a ∈ labels P) :
    IsConnected (edgeImage P a) := by
  obtain ⟨f, i, rfl⟩ := label_side_exists ha
  rw [edgeImage_range]
  exact isConnected_range (continuous_sideCurve P f i)

/-- The exact parameter certificate carries an entire represented side into
a represented target side whenever every old interval parameter has a
corresponding target parameter. It suffices to choose one target occurrence,
because equal labels and equal normalized parameters are quotient generators. -/
private theorem RespectsParameters.edge_subset {P Q : Presentation} {h : Elementary P Q}
    {H : Realization P ≃ₜ Realization Q} (hH : RespectsParameters h H)
    {a b : ℕ} (hb : b ∈ labels Q)
    (hparam : ∀ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Icc (0 : ℝ) 1, h.parameters a t b s) :
    H '' edgeImage P a ⊆ edgeImage Q b := by
  obtain ⟨f, j, hj⟩ := label_side_exists hb
  rintro x ⟨y, ⟨v, i, t, ht, hi, hv, rfl⟩, rfl⟩
  obtain ⟨s, hs, hp⟩ := hparam t ht
  have he := hH v (f, wordPoint (Q.get f) j s) i j t s ht hs (by rwa [hi, hj]) hv rfl
  rw [he]
  exact ⟨(f, wordPoint (Q.get f) j s), j, s, hs, hj, rfl, rfl⟩

private theorem labelMultiplicity_reindexed {P Q : Presentation} (hr : Reindexed P Q) (a : ℕ) :
    labelMultiplicity P a = labelMultiplicity Q a :=
  (hr.occurrences_perm.map Prod.fst).count_eq a

private theorem occurrences_subdivide (P : Presentation) (a b c : ℕ) :
    occurrences (subdivideEdge P a b c) = (occurrences P).flatMap (splitDart a b c) := by
  induction P with
  | nil => rfl
  | cons w P ih =>
    change w.flatMap (splitDart a b c) ++ occurrences (subdivideEdge P a b c) =
      (w ++ occurrences P).flatMap (splitDart a b c)
    rw [List.flatMap_append, ih]

private theorem splitWord_label_count (W : Word) (a b c k : ℕ)
    (ha : a ≠ b) (ha' : a ≠ c) (hbc : b ≠ c)
    (hb : ∀ d ∈ W, d.1 ≠ b) (hc : ∀ d ∈ W, d.1 ≠ c) :
    (((W.flatMap (splitDart a b c)).map Prod.fst).count k) =
      if k = b ∨ k = c then (W.map Prod.fst).count a
      else if k = a then 0 else (W.map Prod.fst).count k := by
  induction W with
  | nil => simp
  | cons d W ih =>
    have hdb := hb d (by simp)
    have hdc := hc d (by simp)
    have hWb := fun e he ↦ hb e (List.mem_cons_of_mem _ he)
    have hWc := fun e he ↦ hc e (List.mem_cons_of_mem _ he)
    rw [List.flatMap_cons, List.map_append, List.count_append, ih hWb hWc]
    rcases d with ⟨d, t⟩
    dsimp at hdb hdc
    by_cases hda : d = a
    · subst d
      cases t <;> by_cases hkb : k = b <;> by_cases hkc : k = c <;> by_cases hka : k = a <;>
        simp_all [splitDart, List.count_cons, Ne.symm hbc, Ne.symm ha, Ne.symm ha', Nat.add_comm] <;>
        simp_all only [ eq_comm, ite_false, Nat.zero_add]
    · by_cases hkb : k = b <;> by_cases hkc : k = c <;> by_cases hka : k = a <;>
        simp_all [splitDart, List.count_cons, Ne.symm hbc, Ne.symm ha, Ne.symm ha', Nat.add_comm]

private theorem labelMultiplicity_edge (P : Presentation) (a b c : ℕ)
    (ha : a ∈ labels P) (hb : b ∉ labels P) (hc : c ∉ labels P) (hbc : b ≠ c) (k : ℕ) :
    labelMultiplicity (subdivideEdge P a b c) k =
      if k = b ∨ k = c then labelMultiplicity P a
      else if k = a then 0 else labelMultiplicity P k := by
  unfold labelMultiplicity
  rw [occurrences_subdivide]
  apply splitWord_label_count
  · intro he; exact hb (he ▸ ha)
  · intro he; exact hc (he ▸ ha)
  · exact hbc
  · intro d hd he
    apply hb
    simp only [labels, List.mem_toFinset, List.mem_map]
    exact ⟨d, hd, he⟩
  · intro d hd he
    apply hc
    simp only [labels, List.mem_toFinset, List.mem_map]
    exact ⟨d, hd, he⟩

private theorem labelMultiplicity_face (L R : Presentation) (U V : Word) (d k : ℕ) :
    labelMultiplicity (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R) k =
      labelMultiplicity (L ++ [U ++ V] ++ R) k + if k = d then 2 else 0 := by
  simp only [labelMultiplicity, occurrences, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.map_append, List.map_cons, List.map_nil,
    List.count_append, List.count_cons, List.count_nil]
  by_cases hk : k = d
  · subst k
    simp
    omega
  · have hk' : d ≠ k := Ne.symm hk
    simp [hk, hk']

private theorem boundaryImage_same_labels {P Q : Presentation} {h : Elementary P Q}
    {H : Realization P ≃ₜ Realization Q} (hH : RespectsParameters h H)
    (hc : ∀ a, labelMultiplicity P a = 1 ↔ labelMultiplicity Q a = 1)
    (hp : ∀ a t, t ∈ Icc (0 : ℝ) 1 → h.parameters a t a t) :
    H '' boundaryImage P = boundaryImage Q := by
  have hf : H '' boundaryImage P ⊆ boundaryImage Q := by
    rintro x ⟨y, ⟨a, ha, hy⟩, rfl⟩
    have haq := (hc a).mp ha
    refine ⟨a, haq, ?_⟩
    apply hH.edge_subset ((labelMultiplicity_pos Q a).mp (by omega)) (fun t ht ↦ ⟨t, ht, hp a t ht⟩)
    exact ⟨y, hy, rfl⟩
  have hb : H.symm '' boundaryImage Q ⊆ boundaryImage P := by
    rintro x ⟨y, ⟨a, ha, hy⟩, rfl⟩
    have hap := (hc a).mpr ha
    refine ⟨a, hap, ?_⟩
    apply hH.symm.edge_subset ((labelMultiplicity_pos P a).mp (by omega))
      (fun t ht ↦ ⟨t, ht, hp a t ht⟩)
    exact ⟨y, hy, rfl⟩
  apply Set.Subset.antisymm hf
  intro x hx
  exact ⟨H.symm x, hb ⟨x, hx, rfl⟩, H.apply_symm_apply x⟩

private theorem boundaryImage_reindex {P Q : Presentation} (hr : Reindexed P Q)
    (H : Realization P ≃ₜ Realization Q) (hH : RespectsParameters (.reindex hr) H) :
    H '' boundaryImage P = boundaryImage Q := by
  apply boundaryImage_same_labels hH
  · intro a
    rw [labelMultiplicity_reindexed hr]
  · intro a t ht
    exact ⟨rfl, rfl⟩

private theorem boundaryImage_face (L R : Presentation) (U V : Word) (d : ℕ)
    (hU : U ≠ []) (hV : V ≠ []) (hd : d ∉ labels (L ++ [U ++ V] ++ R))
    (H : Realization (L ++ [U ++ V] ++ R) ≃ₜ
      Realization (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R))
    (hH : RespectsParameters (.face L R U V d hU hV hd) H) :
    H '' boundaryImage (L ++ [U ++ V] ++ R) =
      boundaryImage (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R) := by
  apply boundaryImage_same_labels hH
  · intro a
    rw [labelMultiplicity_face]
    by_cases he : a = d
    · subst a
      rw [(labelMultiplicity_zero _ _).mpr hd]
      simp
    · simp [he]
  · intro a t ht
    exact ⟨rfl, rfl⟩

private theorem RespectsParameters.boundary_subset {P Q : Presentation} {h : Elementary P Q}
    {H : Realization P ≃ₜ Realization Q} (hH : RespectsParameters h H)
    (hp : ∀ a, labelMultiplicity P a = 1 → ∀ t ∈ Icc (0 : ℝ) 1,
      ∃ b, labelMultiplicity Q b = 1 ∧ ∃ s ∈ Icc (0 : ℝ) 1, h.parameters a t b s) :
    H '' boundaryImage P ⊆ boundaryImage Q := by
  rintro x ⟨y, ⟨a, ha, v, i, t, ht, hi, hv, rfl⟩, rfl⟩
  obtain ⟨b, hb, s, hs, hp⟩ := hp a ha t ht
  obtain ⟨f, j, hj⟩ := label_side_exists ((labelMultiplicity_pos Q b).mp (by omega))
  have he := hH v (f, wordPoint (Q.get f) j s) i j t s ht hs (by rwa [hi, hj]) hv rfl
  refine ⟨b, hb, ?_⟩
  rw [he]
  exact ⟨(f, wordPoint (Q.get f) j s), j, s, hs, hj, rfl, rfl⟩

private theorem boundaryImage_edge (P : Presentation) (a b c : ℕ)
    (ha : a ∈ labels P) (hb : b ∉ labels P) (hc : c ∉ labels P) (hbc : b ≠ c)
    (H : Realization P ≃ₜ Realization (subdivideEdge P a b c))
    (hH : RespectsParameters (.edge P a b c ha hb hc hbc) H) :
    H '' boundaryImage P = boundaryImage (subdivideEdge P a b c) := by
  have hab : a ≠ b := fun h ↦ hb (h ▸ ha)
  have hac : a ≠ c := fun h ↦ hc (h ▸ ha)
  have hcount := labelMultiplicity_edge P a b c ha hb hc hbc
  have hf : H '' boundaryImage P ⊆ boundaryImage (subdivideEdge P a b c) := by
    apply hH.boundary_subset
    intro k hk t ht
    by_cases hka : k = a
    · subst k
      by_cases ht' : t ≤ 1/2
      · refine ⟨b, ?_, 2*t, ⟨by linarith [ht.1], by linarith⟩, Or.inr (Or.inl ⟨rfl, rfl, ht', rfl⟩)⟩
        rw [hcount]
        simp [hk]
      · refine ⟨c, ?_, 2*t-1, ⟨by linarith, by linarith [ht.2]⟩,
          Or.inr (Or.inr ⟨rfl, rfl, by linarith, rfl⟩)⟩
        rw [hcount]
        simp [hk]
    · have hkb : k ≠ b := by intro he; subst k; have := (labelMultiplicity_zero P b).mpr hb; omega
      have hkc : k ≠ c := by intro he; subst k; have := (labelMultiplicity_zero P c).mpr hc; omega
      refine ⟨k, ?_, t, ht, Or.inl ⟨hka, rfl, rfl⟩⟩
      rw [hcount]
      simp [hka, hkb, hkc, hk]
  have hr : H.symm '' boundaryImage (subdivideEdge P a b c) ⊆ boundaryImage P := by
    apply hH.symm.boundary_subset
    intro k hk t ht
    rw [hcount] at hk
    by_cases hkb : k = b
    · subst k
      have hka : labelMultiplicity P a = 1 := by simpa using hk
      refine ⟨a, hka, t/2, ⟨by linarith [ht.1], by linarith [ht.2]⟩,
        Or.inr (Or.inl ⟨rfl, rfl, by linarith [ht.2], by ring⟩)⟩
    · by_cases hkc : k = c
      · subst k
        have hka : labelMultiplicity P a = 1 := by simpa using hk
        refine ⟨a, hka, (t+1)/2, ⟨by linarith [ht.1], by linarith [ht.2]⟩,
          Or.inr (Or.inr ⟨rfl, rfl, by linarith [ht.1], by ring⟩)⟩
      · have hka : k ≠ a := by intro he; simp [he, hab, hac] at hk
        have hkP : labelMultiplicity P k = 1 := by simpa [hkb, hkc, hka] using hk
        exact ⟨k, hkP, t, ht, Or.inl ⟨hka, rfl, rfl⟩⟩
  apply Set.Subset.antisymm hf
  intro x hx
  exact ⟨H.symm x, hr ⟨x, hx, rfl⟩, H.apply_symm_apply x⟩

private theorem labelMultiplicity_rename {P Q : Presentation} (e : ℕ ≃ ℕ) (flip : ℕ → Bool)
    (f : Fin P.length ≃ Fin Q.length)
    (hr : ∀ i, List.IsRotated
      ((P.get i).map fun d ↦ (e d.1, if flip d.1 then !d.2 else d.2)) (Q.get (f i))) (a : ℕ) :
    labelMultiplicity P a = labelMultiplicity Q (e a) := by
  have hw (i : Fin P.length) : ((P.get i).map Prod.fst).count a =
      ((Q.get (f i)).map Prod.fst).count (e a) := by
    have hc := ((hr i).perm.map Prod.fst).count_eq (e a)
    have hm : (((P.get i).map fun d ↦ (e d.1, if flip d.1 then !d.2 else d.2)).map Prod.fst) =
        ((P.get i).map Prod.fst).map e := by simp only [List.map_map, Function.comp_def]
    rw [hm, List.count_map_of_injective _ e e.injective] at hc
    exact hc
  simp only [labelMultiplicity, occurrences, List.map_flatten, List.count_flatten, List.map_map]
  rw [← Fin.sum_univ_fun_getElem, ← Fin.sum_univ_fun_getElem]
  exact Fintype.sum_equiv f _ _ hw

private theorem boundaryImage_rename {P Q : Presentation} (e : ℕ ≃ ℕ) (flip : ℕ → Bool)
    (f : Fin P.length ≃ Fin Q.length)
    (hr : ∀ i, List.IsRotated
      ((P.get i).map fun d ↦ (e d.1, if flip d.1 then !d.2 else d.2)) (Q.get (f i)))
    (H : Realization P ≃ₜ Realization Q)
    (hH : RespectsParameters (.rename e flip f hr) H) :
    H '' boundaryImage P = boundaryImage Q := by
  have hc := labelMultiplicity_rename e flip f hr
  have hf : H '' boundaryImage P ⊆ boundaryImage Q := by
    apply hH.boundary_subset
    intro a ha t ht
    refine ⟨e a, by rwa [← hc], if flip a then 1-t else t, ?_, rfl, rfl⟩
    cases hfa : flip a <;> simp <;> exact ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
  have hb : H.symm '' boundaryImage Q ⊆ boundaryImage P := by
    apply hH.symm.boundary_subset
    intro b hb t ht
    refine ⟨e.symm b, ?_, if flip (e.symm b) then 1-t else t, ?_, e.apply_symm_apply b, ?_⟩
    · simpa only [hc, Equiv.apply_symm_apply] using hb
    · cases hfb : flip (e.symm b) <;> simp <;> exact ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
    · cases hfb : flip (e.symm b) <;> simp
  apply Set.Subset.antisymm hf
  intro x hx
  exact ⟨H.symm x, hb ⟨x, hx, rfl⟩, H.apply_symm_apply x⟩

/-- Every realized elementary move carries the union of unpaired edge images
onto the corresponding union in the target. Source: Gallier–Xu Definition
6.3, pp.84–86, with the exact side-parameter realization of Proposition 3.2
p.31. P1 replaces each old occurrence by one occurrence of each half-label;
a boundary interval therefore becomes its two halves. P2 adds only the two
occurrences of its fresh internal edge, so no boundary label is added or
removed. Reindexing preserves occurrence counts, signed renaming transports
them bijectively, and inverse homeomorphisms reverse these same equalities. -/
private theorem elementary_boundary_image {P Q : Presentation} (h : Elementary P Q)
    (H : Realization P ≃ₜ Realization Q) (hH : RespectsParameters h H) :
    H '' boundaryImage P = boundaryImage Q := by
  induction h with
  | edge P a b c ha hb hc hbc => exact boundaryImage_edge P a b c ha hb hc hbc H hH
  | face L R U V d hU hV hd => exact boundaryImage_face L R U V d hU hV hd H hH
  | inverse h ih =>
    have he := ih H.symm hH.symm
    have hi := congrArg (fun A ↦ H '' A) he
    simpa only [Set.image_image, Homeomorph.apply_symm_apply, Set.image_id'] using hi.symm
  | reindex hr => exact boundaryImage_reindex hr H hH
  | rename e flip f hr => exact boundaryImage_rename e flip f hr H hH

private theorem RealizedSequence.boundary_image {P Q : Presentation} (s : RealizedSequence P Q) :
    s.homeomorph '' boundaryImage P = boundaryImage Q := by
  induction s with
  | nil P => simp [RealizedSequence.homeomorph]
  | cons h H hH tail ih =>
    rw [RealizedSequence.homeomorph]
    change (tail.homeomorph ∘ H) '' boundaryImage _ = _
    calc
      _ = tail.homeomorph '' (H '' boundaryImage _) := (Set.image_image _ _ _).symm
      _ = _ := by rw [elementary_boundary_image h H hH, ih]

private theorem triangle_word_label_count {N : ℕ} {K : AbstractSimplicialComplex (Fin N)}
    (s : Triangle K) (o : Fin 3 ≃ ↥s.val) (u v : Fin N) (huv : u ≠ v) :
    ((triangleWord s o).map Prod.fst).count (edgeLabel u v) =
      if ({u,v} : Finset (Fin N)) ⊆ s.val then 1 else 0 := by
  have hnd : ((triangleWord s o).map Prod.fst).Nodup := by
    simp only [triangleWord, List.map_map, Function.comp_def, edgeDart]
    exact (List.nodup_finRange 3).map (triangle_side_label_injective s o)
  by_cases hs : ({u,v} : Finset (Fin N)) ⊆ s.val
  · rw [ite_eq_left hs]
    apply List.count_eq_one_of_mem hnd
    obtain ⟨i, hi⟩ := triangle_pair_side s o (hs (by simp)) (hs (by simp)) huv
    exact List.mem_map.mpr ⟨_, List.get_mem _ i, hi⟩
  · rw [ite_eq_right hs]
    apply List.count_eq_zero_of_not_mem
    intro hm
    obtain ⟨d, hd, he⟩ := List.mem_map.mp hm
    exact hs (triangle_label_contains_edge s o hd huv he)

/-- The number of occurrences of an original edge label is precisely the
number of original incident triangles. Source: Gallier–Xu Definition 6.1,
pp.79–81. The three side labels of a triangle are distinct. The count in
each triangle is one exactly when both endpoints belong to that triangle,
and zero otherwise; summing these indicators is the defining incidence. -/
private theorem triangle_label_multiplicity {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (u v : Fin N) (huv : u ≠ v) :
    labelMultiplicity (trianglePresentation K o) (edgeLabel u v) = incidence K {u,v} := by
  simp only [labelMultiplicity, occurrences, trianglePresentation, List.map_flatten,
    List.count_flatten, List.map_map, Function.comp_def]
  rw [← List.sum_toFinset _ (Finset.nodup_toList _)]
  simp only [Finset.toList_toFinset]
  have hcount (t : { x // x ∈ simplices K 2 }) :
      ((triangleWord ⟨t.val, by simpa [simplices] using t.property⟩
        (o ⟨t.val, by simpa [simplices] using t.property⟩)).map Prod.fst).count (edgeLabel u v) =
        if ({u,v} : Finset (Fin N)) ⊆ t.val then 1 else 0 :=
    triangle_word_label_count _ _ u v huv
  simp_rw [hcount]
  simp [incidence, Finset.filter_attach]

private theorem original_segment_parameter {N : ℕ} (u v : Fin N) (x : Fin N → ℝ) :
    x ∈ segment ℝ (Pi.single u 1) (Pi.single v 1) ↔
      ∃ t ∈ Icc (0 : ℝ) 1, x = originalEdgePoint u v t := by
  rcases le_total u v with h | h
  · simp only [originalEdgePoint, min_eq_left h, max_eq_right h, segment_eq_image,
      Set.mem_image]
    exact exists_congr fun t ↦ and_congr_right fun _ ↦ eq_comm
  · rw [segment_symm]
    simp only [originalEdgePoint, min_eq_right h, max_eq_left h, segment_eq_image,
      Set.mem_image]
    exact exists_congr fun t ↦ and_congr_right fun _ ↦ eq_comm

private theorem original_edge_image {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (H : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o))
    (hH : OriginalParameters K o H) {u v : Fin N} (huv : u ≠ v)
    (hedge : ({u,v} : Finset (Fin N)) ∈ K.faces)
    (hl : edgeLabel u v ∈ labels (trianglePresentation K o)) :
    H '' {x : ↥(carrier K) | x.val ∈ segment ℝ (Pi.single u 1) (Pi.single v 1)} =
      edgeImage (trianglePresentation K o) (edgeLabel u v) := by
  obtain ⟨f, i, hi⟩ := label_side_exists hl
  rw [← hi, edgeImage_range]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht, he⟩ := (original_segment_parameter u v x.val).mp hx
    refine ⟨⟨t, ht⟩, ?_⟩
    exact (hH x (f, wordPoint _ i t) i u v t huv ht he hi rfl).symm
  · rintro ⟨t, rfl⟩
    let x : ↥(carrier K) := ⟨originalEdgePoint u v t,
      originalEdgePoint_mem_carrier K hedge t.property⟩
    refine ⟨x, (original_segment_parameter u v x.val).mpr ⟨t, t.property, rfl⟩, ?_⟩
    exact hH x (f, wordPoint _ i t) i u v t huv t.property rfl hi rfl

private theorem triangle_label_endpoints {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) {a : ℕ}
    (ha : a ∈ labels (trianglePresentation K o)) :
    ∃ u v : Fin N, u ≠ v ∧ ({u,v} : Finset (Fin N)) ∈ K.faces ∧ a = edgeLabel u v := by
  simp only [labels, List.mem_toFinset, List.mem_map] at ha
  obtain ⟨d, hd, rfl⟩ := ha
  obtain ⟨s, hs⟩ := occurrence_triangle K o hd
  simp only [triangleWord, List.mem_map] at hs
  obtain ⟨i, hi, rfl⟩ := hs
  refine ⟨(o s i).val, (o s (finRotate 3 i)).val, ?_, ?_, rfl⟩
  · intro he
    have hh : ∀ i : Fin 3, i ≠ finRotate 3 i := by decide
    exact hh i ((o s).injective (Subtype.ext he))
  · exact (K.isRelLowerSet_faces s.property.1).2
      (by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff];
          exact ⟨(o s i).property, (o s (finRotate 3 i)).property⟩) (by simp)

/-- Original boundary contours are exactly the singleton-occurrence boundary
trace of the triangle presentation. The incidence count identifies the labels,
and the prescribed original parameters identify their entire edge images. -/
private theorem original_boundary_image {N b : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (H : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o))
    (hH : OriginalParameters K o H) (B : Fin b → List (Fin N))
    (hB : BoundaryCycles K B) :
    H '' (⋃ j, cycleCarrier (K := K) (B j)) = boundaryImage (trianglePresentation K o) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨j, u, v, hc, hx⟩ := Set.mem_iUnion.mp hx
    have he := (hB.2.2 u v).mpr ⟨j, hc⟩
    have hm : labelMultiplicity (trianglePresentation K o) (edgeLabel u v) = 1 := by
      rw [triangle_label_multiplicity K o u v he.1, he.2.2]
    have hl := (labelMultiplicity_pos _ _).mp (hm ▸ Nat.zero_lt_one)
    refine ⟨edgeLabel u v, hm, ?_⟩
    rw [← original_edge_image K o H hH he.1 he.2.1 hl]
    exact ⟨x, hx, rfl⟩
  · rintro ⟨a, ha, hz⟩
    have hl := (labelMultiplicity_pos _ _).mp (ha ▸ Nat.zero_lt_one)
    obtain ⟨u, v, huv, hedge, rfl⟩ := triangle_label_endpoints K o hl
    have he : boundaryEdge K u v := ⟨huv, hedge, by
      rwa [triangle_label_multiplicity K o u v huv] at ha⟩
    obtain ⟨j, hj⟩ := (hB.2.2 u v).mp he
    rw [← original_edge_image K o H hH huv hedge hl] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, Set.mem_iUnion.mpr ⟨j, u, v, hj, hx⟩, rfl⟩

private theorem boundary_cycle_compact_connected {N b : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (B : Fin b → List (Fin N))
    (hB : BoundaryCycles K B) (j : Fin b) :
    IsCompact (cycleCarrier (K := K) (B j)) ∧ IsConnected (cycleCarrier (K := K) (B j)) := by
  obtain ⟨H⟩ := boundaryCycle_circle_homeomorph_g9 K (B j) (hB.1 j).1 (hB.1 j).2
    (fun i ↦ ((hB.2.2 _ _).mpr ⟨j, i, Or.inl ⟨rfl, rfl⟩⟩).2.1)
  exact ⟨isCompact_iff_compactSpace.mpr H.compactSpace,
    isConnected_iff_connectedSpace.mpr (H.connectedSpace_iff.mp inferInstance)⟩

private theorem cycleEdge_mem {N : ℕ} {l : List (Fin N)} {u v : Fin N}
    (h : cycleEdge l u v) : u ∈ l ∧ v ∈ l := by
  obtain ⟨i, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := h <;>
    exact ⟨List.get_mem _ _, List.get_mem _ _⟩

private theorem boundary_cycles_disjoint {N b : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (B : Fin b → List (Fin N))
    (hB : BoundaryCycles K B) {i j : Fin b} (hij : i ≠ j) :
    Disjoint (cycleCarrier (K := K) (B i)) (cycleCarrier (K := K) (B j)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨u, v, hc, hx⟩ ⟨a, b, hd, hy⟩
  have hu := cycleEdge_mem hc
  have ha := cycleEdge_mem hd
  have hn (r : Fin N) (hr : r ∈ B i) (s : Fin N) (hs : s ∈ B j) : r ≠ s := by
    intro he
    subst s
    exact Finset.disjoint_left.mp (hB.2.1 i j hij)
      (List.mem_toFinset.mpr hr) (List.mem_toFinset.mpr hs)
  have hua := hn u hu.1 a ha.1
  have hub := hn u hu.1 b ha.2
  have hva := hn v hu.2 a ha.1
  have hvb := hn v hu.2 b ha.2
  have huv := ((hB.2.2 u v).mpr ⟨i, hc⟩).1
  obtain ⟨r, s, hr, hs, hrs, he⟩ := hx
  obtain ⟨p, q, hp, hq, hpq, hf⟩ := hy
  have heq := he.trans hf.symm
  have her := congrFun heq u
  have hes := congrFun heq v
  simp [Pi.add_apply, Pi.smul_apply, huv, Ne.symm huv,
    hua, hub, hva, hvb] at her hes
  linarith

private theorem scalar_extension_side (W : Word) (hn : 4 ≤ W.length)
    (A : C(Disk, ℝ)) (hA : ∀ z : Circle, A ⟨z, by simp⟩ = handleCircleArgumentG9 W.length hn z)
    (i : Fin W.length) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    A (wordPoint W i t) = handleTentG9 ((i.val : ℝ) + dartParameter (W.get i) t) := by
  let x : ℝ := (i.val : ℝ) + dartParameter (W.get i) t
  have hi : (i.val : ℝ) + 1 ≤ W.length := by exact_mod_cast i.isLt
  have hx : x ∈ Icc (0 : ℝ) W.length := by
    dsimp [x, dartParameter]
    split_ifs <;> constructor <;> nlinarith [ht.1, ht.2, (show (0 : ℝ) ≤ i.val by positivity)]
  change A ⟨(Circle.exp (2*Real.pi*x/W.length) : ℂ), _⟩ = handleTentG9 x
  rw [hA, handleCircleArgument_exp_g9 _ _ _ hx]

private def loopWord (a b : ℕ) (L : Word) : Word := [(a,true),(b,true),(a,false)] ++ L

private theorem loop_scalar_side (a b : ℕ) (hab : a ≠ b) (L : Word)
    (hL : ∀ d ∈ L, d.1 ≠ a ∧ d.1 ≠ b) (hn : 4 ≤ (loopWord a b L).length)
    (A : C(Disk, ℝ))
    (hA : ∀ z : Circle, A ⟨z, by simp⟩ = handleCircleArgumentG9 (loopWord a b L).length hn z)
    (i : Fin (loopWord a b L).length) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    A (wordPoint (loopWord a b L) i t) =
      if ((loopWord a b L).get i).1 = a then t else
        if ((loopWord a b L).get i).1 = b then 1 else 0 := by
  rw [scalar_extension_side _ hn A hA i t ht]
  change handleTentG9 ((i.val : ℝ) + dartParameter ((loopWord a b L)[i.val]) t) = _
  by_cases hi : i.val < 3
  · have hs : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases hs with he | he | he
    · have hg : ((loopWord a b L).get i).1 = a := by
        change (([(a,true),(b,true),(a,false)] ++ L)[i.val]).1 = a
        simp [he]
      rw [hg]
      simpa [loopWord, he, dartParameter] using handleTent_first_g9 t ht
    · have hg : ((loopWord a b L).get i).1 = b := by
        change (([(a,true),(b,true),(a,false)] ++ L)[i.val]).1 = b
        simp [he]
      rw [hg]
      simpa [loopWord, he, dartParameter, Ne.symm hab] using handleTent_second_g9 t ht
    · have hg : ((loopWord a b L).get i).1 = a := by
        change (([(a,true),(b,true),(a,false)] ++ L)[i.val]).1 = a
        simp [he]
      rw [hg]
      simpa [loopWord, he, dartParameter] using handleTent_third_g9 t ht
  · have hin : 3 ≤ i.val := by omega
    have hiL : i.val - 3 < L.length := by have hh := i.isLt; simp [loopWord] at hh; omega
    have hget : (loopWord a b L).get i = L[i.val - 3] := by
      change ([(a,true),(b,true),(a,false)] ++ L)[i.val] = _
      rw [List.getElem_append_right (by simpa using hin)]
      rfl
    have hf := hL _ (List.getElem_mem hiL)
    rw [show ((loopWord a b L)[i.val]) = L[i.val - 3] from hget]
    simp only [hget, hf.1, hf.2, ite_false]
    apply handleTent_of_three_le_g9
    have hir : (3 : ℝ) ≤ i.val := by exact_mod_cast hin
    unfold dartParameter
    split_ifs <;> linarith [ht.1, ht.2]

/-- The scalar trapezoid separates this loop from all other unpaired sides.
The extension on the disk descends because its normalized values agree on
all paired sides. Source: Gallier–Xu normal blocks, pp.88–90. -/
private theorem loop_scalar_map (a b : ℕ) (hab : a ≠ b) (L : Word)
    (hL : ∀ d ∈ L, d.1 ≠ a ∧ d.1 ≠ b) (hne : L ≠ []) :
    ∃ F : C(Realization [loopWord a b L], ℝ),
      ∀ (i : Fin (loopWord a b L).length) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
        F (project [loopWord a b L] (0, wordPoint (loopWord a b L) i t)) =
          if ((loopWord a b L).get i).1 = a then t else
            if ((loopWord a b L).get i).1 = b then 1 else 0 := by
  have hn : 4 ≤ (loopWord a b L).length := by
    have : 0 < L.length := List.length_pos_iff.mpr hne
    simp [loopWord]; omega
  obtain ⟨A, hA⟩ := handleArgument_disk_extension_g9 (loopWord a b L).length hn
  let f : FaceDisks [loopWord a b L] → ℝ := fun x ↦ A x.2
  have hrel (x y : FaceDisks [loopWord a b L])
      (h : edgeIdentification [loopWord a b L] x y) : f x = f y := by
    obtain ⟨xf,x⟩ := x
    obtain ⟨yf,y⟩ := y
    have hxf : xf = 0 := Fin.eq_zero xf
    have hyf : yf = 0 := Fin.eq_zero yf
    subst xf; subst yf
    obtain ⟨i,j,t,ht,hl,hx,hy⟩ := h
    have hxd : x = wordPoint (loopWord a b L) i t := Subtype.ext hx
    have hyd : y = wordPoint (loopWord a b L) j t := Subtype.ext hy
    change A x = A y
    rw [hxd, hyd, loop_scalar_side a b hab L hL hn A hA i t ht,
      loop_scalar_side a b hab L hL hn A hA j t ht]
    change ((loopWord a b L).get i).1 = ((loopWord a b L).get j).1 at hl
    rw [hl]
  have heq (x y : FaceDisks [loopWord a b L])
      (h : Relation.EqvGen (edgeIdentification [loopWord a b L]) x y) : f x = f y := by
    induction h with
    | rel a b hab => exact hrel a b hab
    | refl a => rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ih1 ih2 => exact ih1.trans ih2
  refine ⟨⟨Quotient.lift f heq, (A.continuous.comp continuous_snd).quotient_lift heq⟩, ?_⟩
  intro i t ht
  exact loop_scalar_side a b hab L hL hn A hA i t ht

private theorem loop_edge_disjoint (a b k : ℕ) (hab : a ≠ b) (L : Word)
    (hL : ∀ d ∈ L, d.1 ≠ a ∧ d.1 ≠ b) (hne : L ≠ [])
    (hka : k ≠ a) (hkb : k ≠ b) :
    Disjoint (edgeImage [loopWord a b L] b) (edgeImage [loopWord a b L] k) := by
  obtain ⟨F, hF⟩ := loop_scalar_map a b hab L hL hne
  have hv (r : ℕ) (hr : r ≠ a) (x : Realization [loopWord a b L])
      (hx : x ∈ edgeImage [loopWord a b L] r) : F x = if r = b then 1 else 0 := by
    obtain ⟨⟨f,z⟩, i, t, ht, hi, hz, rfl⟩ := hx
    have hf : f = 0 := Fin.eq_zero f
    subst f
    have he : z = wordPoint (loopWord a b L) i t := Subtype.ext hz
    rw [he, hF i t ht]
    change ((loopWord a b L).get i).1 = r at hi
    rw [hi, ite_eq_right hr]
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' := hv b (Ne.symm hab) x hx
  have hy' := hv k hka x hy
  simp only [ite_true] at hx'
  rw [ite_eq_right hkb] at hy'
  linarith

private theorem rotation_edge_image {P Q : Presentation} (h : Reindexed P Q)
    (H : Realization P ≃ₜ Realization Q) (hH : RespectsParameters (.reindex h) H)
    (a : ℕ) (ha : a ∈ labels P) : H '' edgeImage P a = edgeImage Q a := by
  have haQ : a ∈ labels Q := (labelMultiplicity_pos Q a).mp (by
    rw [← labelMultiplicity_reindexed h a]
    exact (labelMultiplicity_pos P a).mpr ha)
  apply Set.Subset.antisymm
  · apply hH.edge_subset haQ
    intro t ht
    exact ⟨t, ht, ⟨rfl, rfl⟩⟩
  · have hr := hH.symm
    have hh : H.symm '' edgeImage Q a ⊆ edgeImage P a := by
      apply hr.edge_subset ha
      intro t ht
      exact ⟨t, ht, ⟨rfl, rfl⟩⟩
    intro x hx
    exact ⟨H.symm x, hh ⟨x, hx, rfl⟩, H.apply_symm_apply x⟩

private theorem normal_boundary_image (g b : ℕ) :
    boundaryImage [normalWord g b] = ⋃ j : Fin b, edgeImage [normalWord g b] (2*g+2*j.val+1) := by
  ext x
  simp only [boundaryImage, Set.mem_ofPred_eq, Set.mem_iUnion, normal_boundary_labels]
  constructor
  · rintro ⟨a, ⟨j, rfl⟩, hx⟩
    exact ⟨j, hx⟩
  · rintro ⟨j, hx⟩
    exact ⟨_, ⟨j, rfl⟩, hx⟩

private theorem normal_loop_split (g b : ℕ) (j : Fin b) :
    ∃ U V : Word, normalWord g b = U ++ [(2*g+2*j.val,true),
      (2*g+2*j.val+1,true),(2*g+2*j.val,false)] ++ V := by
  obtain ⟨L, R, hr, _⟩ := List.eq_append_cons_of_mem (List.mem_range.mpr j.isLt)
  refine ⟨((List.range g).flatMap fun i ↦ [(2*i,true),(2*i+1,true),(2*i,false),(2*i+1,false)]) ++
      L.flatMap (fun k ↦ [(2*g+2*k,true),(2*g+2*k+1,true),(2*g+2*k,false)]),
    R.flatMap (fun k ↦ [(2*g+2*k,true),(2*g+2*k+1,true),(2*g+2*k,false)]), ?_⟩
  simp only [normalWord, hr, List.flatMap_append, List.flatMap_cons, List.append_assoc]

private theorem loop_split_fresh {W U V : Word} {a b : ℕ} (hab : a ≠ b)
    (hW : W = U ++ [(a,true),(b,true),(a,false)] ++ V)
    (ha : labelMultiplicity [W] a = 2) (hb : labelMultiplicity [W] b = 1) :
    ∀ d ∈ V ++ U, d.1 ≠ a ∧ d.1 ≠ b := by
  have hca : ((V ++ U).map Prod.fst).count a = 0 := by
    simp only [labelMultiplicity, occurrences, List.flatten_cons, List.flatten_nil,
      List.append_nil, hW, List.map_append, List.count_append, List.map_cons,
      List.map_nil, List.count_cons, List.count_nil, beq_iff_eq] at ha
    simp only [List.map_append, List.count_append]
    simp only [ Ne.symm hab, ite_true, ite_false] at ha
    omega
  have hcb : ((V ++ U).map Prod.fst).count b = 0 := by
    simp only [labelMultiplicity, occurrences, List.flatten_cons, List.flatten_nil,
      List.append_nil, hW, List.map_append, List.count_append, List.map_cons,
      List.map_nil, List.count_cons, List.count_nil, beq_iff_eq] at hb
    simp only [List.map_append, List.count_append]
    simp only [hab, ite_true, ite_false] at hb
    omega
  intro d hd
  constructor
  · intro he
    exact List.count_eq_zero.mp hca (List.mem_map.mpr ⟨d, hd, he⟩)
  · intro he
    exact List.count_eq_zero.mp hcb (List.mem_map.mpr ⟨d, hd, he⟩)

private theorem normal_boundary_disjoint (g b : ℕ) {j k : Fin b} (hjk : j ≠ k) :
    Disjoint (edgeImage [normalWord g b] (2*g+2*j.val+1))
      (edgeImage [normalWord g b] (2*g+2*k.val+1)) := by
  have hjk' : j.val ≠ k.val := fun h ↦ hjk (Fin.ext h)
  obtain ⟨U, V, hW⟩ := normal_loop_split g b j
  have ha : labelMultiplicity [normalWord g b] (2*g+2*j.val) = 2 := by
    rw [normal_label_multiplicity]
    have := j.isLt
    split_ifs <;> omega
  have hb := normalWord_boundary_label_count (g := g) j.isLt
  have hab : 2*g+2*j.val ≠ 2*g+2*j.val+1 := by omega
  have hf := loop_split_fresh hab hW ha hb
  have hne : V ++ U ≠ [] := by
    intro he
    have hlen := congrArg List.length hW
    have hvu := congrArg List.length he
    rw [normalWord_length] at hlen
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen hvu
    have := j.isLt
    have := k.isLt
    omega
  have hr : Reindexed [normalWord g b] [loopWord (2*g+2*j.val) (2*g+2*j.val+1) (V++U)] := by
    apply reindexed_singleton
    rw [hW]
    simpa only [loopWord, List.append_assoc] using
      (List.isRotated_append (l := U)
        (l' := [(2*g+2*j.val,true),(2*g+2*j.val+1,true),(2*g+2*j.val,false)] ++ V))
  obtain ⟨H, hH⟩ := reindex_realized hr
  have hlabel (i : Fin b) : 2*g+2*i.val+1 ∈ labels [normalWord g b] := by
    rw [normalWord_labels, Finset.mem_range]
    have := i.isLt
    omega
  have hleft := rotation_edge_image hr H hH _ (hlabel j)
  have hright := rotation_edge_image hr H hH _ (hlabel k)
  have hd := loop_edge_disjoint (2*g+2*j.val) (2*g+2*j.val+1) (2*g+2*k.val+1)
    hab (V++U) hf hne (by omega) (by omega)
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply Set.disjoint_left.mp hd
  · rw [← hleft]
    exact ⟨x, hx, rfl⟩
  · rw [← hright]
    exact ⟨x, hy, rfl⟩

private theorem connected_subset_finite_disjoint {X I : Type*} [TopologicalSpace X] [Finite I]
    (T : I → Set X) (hclosed : ∀ i, IsClosed (T i))
    (hdis : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    {S : Set X} (hS : IsConnected S) (hsub : S ⊆ ⋃ i, T i) : ∃ i, S ⊆ T i := by
  obtain ⟨x, hx⟩ := hS.nonempty
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hsub hx)
  refine ⟨i, ?_⟩
  intro y hy
  by_contra hiy
  let V : Set X := ⋃ j : {j : I // j ≠ i}, T j.val
  have hV : IsClosed V := isClosed_iUnion_of_finite fun j ↦ hclosed j.val
  have hSV : S ⊆ T i ∪ V := by
    intro z hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hsub hz)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨j,hji⟩, hj⟩)
  have hyV : y ∈ V := (hSV hy).resolve_left hiy
  obtain ⟨z, hzS, hzi, hzV⟩ := isPreconnected_closed_iff.mp hS.isPreconnected
    (T i) V (hclosed i) hV hSV ⟨x,hx,hi⟩ ⟨y,hy,hyV⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hzV
  exact Set.disjoint_left.mp (hdis i j.val (Ne.symm j.property)) hzi hj

/-- Two finite decompositions of the same space into nonempty disjoint closed
connected sets coincide up to a bijection. Connectedness places each piece
inside one piece of the other decomposition; doing this twice and using a
point of the first piece forces equality. -/
private theorem finite_connected_partition_equiv {X I J : Type*}
    [TopologicalSpace X] [Finite I] [Finite J]
    (S : I → Set X) (T : J → Set X)
    (hSc : ∀ i, IsConnected (S i)) (hTc : ∀ j, IsConnected (T j))
    (hSclosed : ∀ i, IsClosed (S i)) (hTclosed : ∀ j, IsClosed (T j))
    (hSd : ∀ i k, i ≠ k → Disjoint (S i) (S k))
    (hTd : ∀ j k, j ≠ k → Disjoint (T j) (T k))
    (hu : (⋃ i, S i) = ⋃ j, T j) : ∃ e : I ≃ J, ∀ i, S i = T (e i) := by
  have hST (i : I) : ∃ j, S i ⊆ T j :=
    connected_subset_finite_disjoint T hTclosed hTd (hSc i) (by
      intro x hx; rw [← hu]; exact Set.mem_iUnion.mpr ⟨i,hx⟩)
  have hTS (j : J) : ∃ i, T j ⊆ S i :=
    connected_subset_finite_disjoint S hSclosed hSd (hTc j) (by
      intro x hx; rw [hu]; exact Set.mem_iUnion.mpr ⟨j,hx⟩)
  choose f hf using hST
  choose g hg using hTS
  have hgf (i : I) : g (f i) = i := by
    by_contra he
    obtain ⟨x,hx⟩ := (hSc i).nonempty
    exact Set.disjoint_left.mp (hSd i (g (f i)) (Ne.symm he)) hx (hg _ (hf _ hx))
  have hfg (j : J) : f (g j) = j := by
    by_contra he
    obtain ⟨x,hx⟩ := (hTc j).nonempty
    exact Set.disjoint_left.mp (hTd j (f (g j)) (Ne.symm he)) hx (hf _ (hg _ hx))
  let e : I ≃ J := ⟨f,g,hgf,hfg⟩
  refine ⟨e, fun i ↦ Set.Subset.antisymm (hf i) ?_⟩
  have hh := hg (f i)
  rwa [hgf i] at hh

private theorem boundary_normal_equiv {N b g c : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (B : Fin b → List (Fin N))
    (hB : BoundaryCycles K B)
    (H : ↥(carrier K) ≃ₜ Realization [normalWord g c])
    (hH : H '' (⋃ j, cycleCarrier (K := K) (B j)) = boundaryImage [normalWord g c]) :
    ∃ e : Fin b ≃ Fin c, ∀ j, H '' cycleCarrier (K := K) (B j) =
      edgeImage [normalWord g c] (2*g+2*(e j).val+1) := by
  let : T2Space (Realization [normalWord g c]) := H.t2Space
  apply finite_connected_partition_equiv
    (fun j : Fin b ↦ H '' cycleCarrier (K := K) (B j))
    (fun j : Fin c ↦ edgeImage [normalWord g c] (2*g+2*j.val+1))
  · intro j
    exact (boundary_cycle_compact_connected K B hB j).2.image _ H.continuous.continuousOn
  · intro j
    apply edgeImage_connected
    rw [normalWord_labels, Finset.mem_range]
    have := j.isLt
    omega
  · intro j
    exact ((boundary_cycle_compact_connected K B hB j).1.image H.continuous).isClosed
  · intro j
    exact (edgeImage_compact _ _).isClosed
  · intro i j hij
    exact Set.disjoint_image_of_injective H.injective (boundary_cycles_disjoint K B hB hij)
  · intro i j hij
    exact normal_boundary_disjoint g c hij
  · rw [← Set.image_iUnion, hH, normal_boundary_image]

private theorem sequence_to_normal_boundary {N b g c : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (H₀ : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o))
    (hH₀ : OriginalParameters K o H₀)
    (B : Fin b → List (Fin N)) (hB : BoundaryCycles K B)
    (s : RealizedSequence (trianglePresentation K o) [normalWord g c]) :
    ∃ e : Fin b ≃ Fin c, ∀ j,
      (H₀.trans s.homeomorph) '' cycleCarrier (K := K) (B j) =
        edgeImage [normalWord g c] (2*g+2*(e j).val+1) := by
  apply boundary_normal_equiv K B hB (H₀.trans s.homeomorph)
  change (s.homeomorph ∘ H₀) '' _ = _
  calc
    _ = s.homeomorph '' (H₀ '' (⋃ j, cycleCarrier (K := K) (B j))) := (Set.image_image _ _ _).symm
    _ = _ := by rw [original_boundary_image K o H₀ hH₀ B hB, s.boundary_image]

/-- Incoming endpoint classes of the literal polygon corner relation. -/
private def vertexSetoid (P : Presentation) : Setoid Dart := Relation.EqvGen.setoid (corner P)

private def vertexDarts (P : Presentation) : Finset Dart := labels P ×ˢ Finset.univ

private def vertexClasses (P : Presentation) : Finset (Quotient (vertexSetoid P)) :=
  (vertexDarts P).image (Quotient.mk (vertexSetoid P))

private def vertexCount (P : Presentation) : ℕ := (vertexClasses P).card

private theorem vertexDarts_mem (P : Presentation) (d : Dart) :
    d ∈ vertexDarts P ↔ d.1 ∈ labels P := by simp [vertexDarts]

private theorem corner_labels {P : Presentation} {a b : Dart} (h : corner P a b) :
    a.1 ∈ labels P ∧ b.1 ∈ labels P := by
  obtain ⟨f, i, rfl, rfl⟩ := h
  have hh (j : Fin (P.get f).length) : ((P.get f).get j).1 ∈ labels P := by
    simp only [labels, List.mem_toFinset, List.mem_map]
    exact ⟨_, List.mem_flatten.mpr ⟨_, List.get_mem _ f, List.get_mem _ j⟩, rfl⟩
  exact ⟨hh i, hh _⟩

private theorem sameVertex_labels {P : Presentation} {a b : Dart}
    (h : sameVertex P a b) : a.1 ∈ labels P ↔ b.1 ∈ labels P := by
  induction h with
  | rel a b hab => exact iff_of_true (corner_labels hab).1 (corner_labels hab).2
  | refl a => rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ih ih' => exact ih.trans ih'

/-- A complete finite classifier of incoming corners counts the actual
vertices. Surjectivity supplies every class, while the same-vertex criterion
makes the induced map on the finite quotient both well-defined and injective. -/
private theorem vertexCount_of_classifier {A : Type*} [Fintype A]
    (P : Presentation) (f : Dart → A)
    (hc : ∀ a b, corner P a b → f a = f b)
    (hi : ∀ a ∈ vertexDarts P, ∀ b ∈ vertexDarts P, f a = f b → sameVertex P a b)
    (hs : ∀ x, ∃ a ∈ vertexDarts P, f a = x) : vertexCount P = Fintype.card A := by
  let F : Quotient (vertexSetoid P) → A := Quotient.lift f (fun _ _ h ↦ sameVertex_map_eq f hc h)
  have hmap : (vertexClasses P).image F = Finset.univ := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, iff_true]
    obtain ⟨a, ha, he⟩ := hs x
    exact ⟨Quotient.mk _ a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, he⟩
  have hinj : Set.InjOn F (vertexClasses P) := by
    intro x hx y hy he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact Quotient.sound (hi a ha b hb he)
  have hcard := Finset.card_image_of_injOn hinj
  rw [hmap, Finset.card_univ] at hcard
  exact hcard.symm

private theorem corner_iff_word {P : Presentation} {a b : Dart} :
    corner P a b ↔ ∃ W ∈ P, corner [W] a b := by
  constructor
  · rintro ⟨j, i, hi, hj⟩
    exact ⟨P.get j, List.get_mem _ _, 0, i, hi, hj⟩
  · rintro ⟨W, hW, j, i, hi, hj⟩
    have hj0 : j = 0 := Fin.eq_zero j
    subst j
    obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hW
    exact ⟨k, i, hi, hj⟩

private theorem corner_compatible_words {A : Type*} (P : Presentation) (f : Dart → A) :
    (∀ a b, corner P a b → f a = f b) ↔
      ∀ W ∈ P, ∀ a b, corner [W] a b → f a = f b := by
  constructor
  · intro h W hW a b hab
    exact h a b (corner_iff_word.mpr ⟨W, hW, hab⟩)
  · intro h a b hab
    obtain ⟨W, hW, hab⟩ := corner_iff_word.mp hab
    exact h W hW a b hab

private theorem corner_compatible_append {A : Type*} (P Q : Presentation) (f : Dart → A) :
    (∀ a b, corner (P ++ Q) a b → f a = f b) ↔
      (∀ a b, corner P a b → f a = f b) ∧
      (∀ a b, corner Q a b → f a = f b) := by
  rw [corner_compatible_words (P ++ Q), corner_compatible_words P, corner_compatible_words Q]
  constructor
  · intro h
    exact ⟨fun W hW ↦ h W (List.mem_append_left Q hW),
      fun W hW ↦ h W (List.mem_append_right P hW)⟩
  · rintro ⟨hP, hQ⟩ W hW
    rcases List.mem_append.mp hW with hW | hW
    · exact hP W hW
    · exact hQ W hW

private theorem incoming_chain_last {A : Type*} (f : Dart → A) (W : Word) (a b : Dart)
    (h : f (inverse a) = f (inverse b)) :
    List.IsChain (fun d e ↦ f d = f (inverse e)) (W ++ [a]) ↔
      List.IsChain (fun d e ↦ f d = f (inverse e)) (W ++ [b]) := by
  simp only [List.isChain_append, List.isChain_singleton, List.head?_cons,
    Option.mem_some_iff, forall_eq', true_and]
  rw [h]

private theorem face_compatible_iff {A : Type*} (f : Dart → A)
    (u v : Dart) (U V : Word) (d : ℕ) :
    (∀ a b, corner [(u :: U) ++ [(d, true)], (d, false) :: v :: V] a b → f a = f b) ↔
      (∀ a b, corner [(u :: U) ++ (v :: V)] a b → f a = f b) ∧
      f (d, true) = f (inverse u) ∧ f (d, false) = f (inverse v) := by
  have hc : (∀ a b, corner [(u :: U) ++ [(d, true)], (d, false) :: v :: V] a b → f a = f b) ↔
      (List.IsChain (fun a b ↦ f a = f (inverse b)) ((u :: U) ++ [(d, true)]) ∧
        f (d, true) = f (inverse u)) ∧
      (f (d, false) = f (inverse v) ∧
        List.IsChain (fun a b ↦ f a = f (inverse b)) ((v :: V) ++ [(d, false)])) := by
    rw [show [(u :: U) ++ [(d, true)], (d, false) :: v :: V] =
      [(u :: U) ++ [(d, true)]] ++ [(d, false) :: v :: V] from rfl,
      corner_compatible_append]
    simp only [List.cons_append, corner_compatible_chain, List.append_assoc,
      List.nil_append, List.isChain_cons_append_cons_cons, List.isChain_singleton,
      and_true, List.isChain_cons_cons]
  have ho : (∀ a b, corner [(u :: U) ++ (v :: V)] a b → f a = f b) ↔
      List.IsChain (fun a b ↦ f a = f (inverse b)) ((u :: U) ++ [v]) ∧
      List.IsChain (fun a b ↦ f a = f (inverse b)) ((v :: V) ++ [u]) := by
    simp only [List.cons_append, corner_compatible_chain, List.append_assoc]
    exact List.isChain_cons_split
  rw [hc, ho]
  constructor
  · rintro ⟨⟨hU, hp⟩, hn, hV⟩
    refine ⟨⟨?_, ?_⟩, hp, hn⟩
    · exact (incoming_chain_last f _ (d, true) v (by simpa [inverse] using hn)).mp hU
    · exact (incoming_chain_last f _ (d, false) u (by simpa [inverse] using hp)).mp hV
  · rintro ⟨⟨hU, hV⟩, hp, hn⟩
    refine ⟨⟨?_, hp⟩, hn, ?_⟩
    · exact (incoming_chain_last f _ (d, true) v (by simpa [inverse] using hn)).mpr hU
    · exact (incoming_chain_last f _ (d, false) u (by simpa [inverse] using hp)).mpr hV

private theorem vertexCount_transport {P Q : Presentation} (f g : Dart → Dart)
    (hf : ∀ a b, corner P a b → sameVertex Q (f a) (f b))
    (hg : ∀ a b, corner Q a b → sameVertex P (g a) (g b))
    (hfm : ∀ a ∈ vertexDarts P, f a ∈ vertexDarts Q)
    (hgm : ∀ a ∈ vertexDarts Q, g a ∈ vertexDarts P)
    (hgf : ∀ a ∈ vertexDarts P, sameVertex P (g (f a)) a)
    (hfg : ∀ a ∈ vertexDarts Q, sameVertex Q (f (g a)) a) :
    vertexCount P = vertexCount Q := by
  let F : Quotient (vertexSetoid P) → Quotient (vertexSetoid Q) :=
    Quotient.lift (fun a ↦ Quotient.mk _ (f a)) (by
      intro a b hab
      exact sameVertex_map_eq _ (fun a b h ↦ Quotient.sound (hf a b h)) hab)
  let G : Quotient (vertexSetoid Q) → Quotient (vertexSetoid P) :=
    Quotient.lift (fun a ↦ Quotient.mk _ (g a)) (by
      intro a b hab
      exact sameVertex_map_eq _ (fun a b h ↦ Quotient.sound (hg a b h)) hab)
  have himage : (vertexClasses P).image F = vertexClasses Q := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨f a, hfm a ha, rfl⟩
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨Quotient.mk _ (g a),
        Finset.mem_image.mpr ⟨g a, hgm a ha, rfl⟩, Quotient.sound (hfg a ha)⟩
  have hinj : Set.InjOn F (vertexClasses P) := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have he := congrArg G hxy
    change Quotient.mk _ (g (f a)) = Quotient.mk _ (g (f b)) at he
    exact (Quotient.sound (hgf a ha)).symm.trans (he.trans (Quotient.sound (hgf b hb)))
  have hcard := Finset.card_image_of_injOn hinj
  rw [himage] at hcard
  exact hcard.symm

private theorem face_context_compatible_iff {A : Type*} (f : Dart → A)
    (L R : Presentation) (u v : Dart) (U V : Word) (d : ℕ) :
    (∀ a b, corner (L ++ [(u :: U) ++ [(d, true)], (d, false) :: v :: V] ++ R) a b → f a = f b) ↔
      (∀ a b, corner (L ++ [(u :: U) ++ (v :: V)] ++ R) a b → f a = f b) ∧
      f (d, true) = f (inverse u) ∧ f (d, false) = f (inverse v) := by
  simp only [corner_compatible_append, face_compatible_iff]
  tauto

private theorem face_subdivision_vertexCount (L R : Presentation) (U V : Word) (d : ℕ)
    (hU : U ≠ []) (hV : V ≠ []) (hd : d ∉ labels (L ++ [U ++ V] ++ R)) :
    vertexCount (L ++ [U ++ V] ++ R) =
      vertexCount (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R) := by
  cases U with
  | nil => exact (hU rfl).elim
  | cons u U =>
    cases V with
    | nil => exact (hV rfl).elim
    | cons v V =>
      let P : Presentation := L ++ [(u :: U) ++ (v :: V)] ++ R
      let Q : Presentation := L ++ [(u :: U) ++ [(d, true)], (d, false) :: v :: V] ++ R
      let πP : Dart → Quotient (vertexSetoid P) := Quotient.mk _
      let πQ : Dart → Quotient (vertexSetoid Q) := Quotient.mk _
      let collapse : Dart → Dart := fun a ↦ if a.1 = d then
        if a.2 then inverse u else inverse v else a
      have hu : u.1 ∈ labels P := by simp [P, labels, occurrences]
      have hv : v.1 ∈ labels P := by simp [P, labels, occurrences]
      have hud : u.1 ≠ d := fun he ↦ hd (he ▸ hu)
      have hvd : v.1 ≠ d := fun he ↦ hd (he ▸ hv)
      have hlabel (a : ℕ) : a ∈ labels Q ↔ a = d ∨ a ∈ labels P := by
        simp only [Q, P, labels, occurrences, List.flatten_append, List.flatten_cons,
          List.flatten_nil, List.append_nil, List.map_append, List.map_cons,
          List.map_nil, List.mem_toFinset, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false]
        tauto
      have hcollapse (a : Dart) (ha : a.1 ∈ labels P) : collapse a = a := by
        have had : a.1 ≠ d := fun he ↦ hd (he ▸ ha)
        simp [collapse, had]
      have hπQ : ∀ a b, corner Q a b → πQ a = πQ b :=
        fun _ _ h ↦ Quotient.sound (Relation.EqvGen.rel _ _ h)
      have hQdata := (face_context_compatible_iff πQ L R u v U V d).mp hπQ
      have hPcollapse : ∀ a b, corner P a b → πP (collapse a) = πP (collapse b) := by
        intro a b hab
        rw [hcollapse a (corner_labels hab).1, hcollapse b (corner_labels hab).2]
        exact Quotient.sound (Relation.EqvGen.rel _ _ hab)
      have hQcollapse : ∀ a b, corner Q a b → πP (collapse a) = πP (collapse b) := by
        apply (face_context_compatible_iff (πP ∘ collapse) L R u v U V d).mpr
        refine ⟨hPcollapse, ?_, ?_⟩ <;> simp [ collapse, inverse, hud, hvd]
      apply vertexCount_transport id collapse
      · intro a b hab
        exact Quotient.exact (hQdata.1 a b hab)
      · intro a b hab
        exact Quotient.exact (hQcollapse a b hab)
      · intro a ha
        exact (vertexDarts_mem Q a).mpr ((hlabel a.1).mpr (Or.inr ((vertexDarts_mem P a).mp ha)))
      · intro a ha
        apply (vertexDarts_mem P (collapse a)).mpr
        rcases (hlabel a.1).mp ((vertexDarts_mem Q a).mp ha) with he | hm
        · cases hs : a.2
          · simpa [collapse, he, hs, inverse] using hv
          · simpa [collapse, he, hs, inverse] using hu
        · rw [hcollapse a hm]
          exact hm
      · intro a ha
        change sameVertex P (collapse a) a
        rw [hcollapse a ((vertexDarts_mem P a).mp ha)]
        exact Relation.EqvGen.refl _
      · intro a ha
        change sameVertex Q (collapse a) a
        by_cases he : a.1 = d
        · obtain ⟨a, s⟩ := a
          simp only [] at he
          subst a
          cases s
          · simpa [collapse, sameVertex] using (Quotient.exact hQdata.2.2).symm
          · simpa [collapse, sameVertex] using (Quotient.exact hQdata.2.1).symm
        · simp only [collapse, he, ite_false]
          exact Relation.EqvGen.refl _

private theorem corner_compatible_cons_rotate {A : Type*} (f : Dart → A) (a : Dart) (W : Word) :
    (∀ d e, corner [a :: W] d e → f d = f e) ↔
      (∀ d e, corner [W ++ [a]] d e → f d = f e) := by
  cases W with
  | nil => rfl
  | cons b W =>
    simp only [List.cons_append, corner_compatible_chain, List.append_assoc,
      List.isChain_cons_cons, List.nil_append, List.isChain_cons_append_cons_cons,
      List.isChain_singleton, and_true]
    exact and_comm

private theorem corner_compatible_rotate {A : Type*} (f : Dart → A) (W : Word) (n : ℕ) :
    (∀ d e, corner [W.rotate n] d e → f d = f e) ↔
      (∀ d e, corner [W] d e → f d = f e) := by
  induction n generalizing W with
  | zero => simp
  | succ n ih =>
    cases W with
    | nil => simp
    | cons a W =>
      rw [List.rotate_cons_succ, ih, ← corner_compatible_cons_rotate]

private theorem corner_compatible_rotated {A : Type*} (f : Dart → A)
    {W W' : Word} (h : W.IsRotated W') :
    (∀ d e, corner [W] d e → f d = f e) ↔
      (∀ d e, corner [W'] d e → f d = f e) := by
  obtain ⟨n, rfl⟩ := h
  exact (corner_compatible_rotate f W n).symm

private theorem corner_compatible_reindexed {A : Type*} (f : Dart → A)
    {P Q : Presentation} (h : Reindexed P Q) :
    (∀ a b, corner P a b → f a = f b) ↔
      (∀ a b, corner Q a b → f a = f b) := by
  obtain ⟨e, he⟩ := h
  rw [corner_compatible_words, corner_compatible_words]
  constructor
  · intro h W hW
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hW
    have hi := h (P.get (e.symm i)) (List.get_mem _ _)
    have hr := (corner_compatible_rotated f (he (e.symm i))).mp hi
    simpa using hr
  · intro h W hW
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hW
    exact (corner_compatible_rotated f (he i)).mpr (h _ (List.get_mem _ _))

private theorem vertexCount_reindexed {P Q : Presentation} (h : Reindexed P Q) :
    vertexCount P = vertexCount Q := by
  have hcP : ∀ a b, corner P a b → Quotient.mk (vertexSetoid P) a = Quotient.mk _ b :=
    fun _ _ h ↦ Quotient.sound (Relation.EqvGen.rel _ _ h)
  have hcQ : ∀ a b, corner Q a b → Quotient.mk (vertexSetoid Q) a = Quotient.mk _ b :=
    fun _ _ h ↦ Quotient.sound (Relation.EqvGen.rel _ _ h)
  have hm (a : Dart) : a ∈ vertexDarts P ↔ a ∈ vertexDarts Q := by
    simp only [vertexDarts_mem, ← labelMultiplicity_pos]
    rw [labelMultiplicity_reindexed h]
  apply vertexCount_transport id id
  · intro a b hab
    exact Quotient.exact ((corner_compatible_reindexed _ h).mpr hcQ a b hab)
  · intro a b hab
    exact Quotient.exact ((corner_compatible_reindexed _ h).mp hcP a b hab)
  · exact fun a ha ↦ (hm a).mp ha
  · exact fun a ha ↦ (hm a).mpr ha
  · exact fun a _ ↦ Relation.EqvGen.refl a
  · exact fun a _ ↦ Relation.EqvGen.refl a

private theorem corner_compatible_word_map {A : Type*} (f : Dart → A)
    (r : Dart → Dart) (hr : ∀ a, r (inverse a) = inverse (r a)) (W : Word) :
    (∀ a b, corner [W.map r] a b → f a = f b) ↔
      (∀ a b, corner [W] a b → f (r a) = f (r b)) := by
  cases W with
  | nil => simp [corner]
  | cons a W =>
    simp only [List.map_cons, corner_compatible_chain]
    rw [show (r a :: W.map r) ++ [r a] = ((a :: W) ++ [a]).map r by simp,
      List.isChain_map]
    simp only [ hr]

private theorem corner_compatible_map {A : Type*} (f : Dart → A)
    (r : Dart → Dart) (hr : ∀ a, r (inverse a) = inverse (r a)) (P : Presentation) :
    (∀ a b, corner (P.map (List.map r)) a b → f a = f b) ↔
      (∀ a b, corner P a b → f (r a) = f (r b)) := by
  rw [corner_compatible_words (P.map (List.map r)), corner_compatible_words P]
  constructor
  · intro h W hW
    exact (corner_compatible_word_map f r hr W).mp (h _ (List.mem_map.mpr ⟨W, hW, rfl⟩))
  · intro h W hW
    obtain ⟨Z, hZ, he⟩ := List.mem_map.mp hW
    subst W
    exact (corner_compatible_word_map f r hr Z).mpr (h Z hZ)

private def signedDartEquiv (e : ℕ ≃ ℕ) (flip : ℕ → Bool) : Dart ≃ Dart where
  toFun a := (e a.1, if flip a.1 then !a.2 else a.2)
  invFun a := (e.symm a.1, if flip (e.symm a.1) then !a.2 else a.2)
  left_inv a := by cases a with | mk a s => cases h : flip a <;> simp [h]
  right_inv a := by cases a with | mk a s => cases h : flip (e.symm a) <;> simp [h]

private theorem signedDartEquiv_inverse (e : ℕ ≃ ℕ) (flip : ℕ → Bool) (a : Dart) :
    signedDartEquiv e flip (inverse a) = inverse (signedDartEquiv e flip a) := by
  cases a with
  | mk a s => cases h : flip a <;> simp [signedDartEquiv, inverse, h]

private theorem vertexCount_signed_map (P : Presentation) (e : ℕ ≃ ℕ) (flip : ℕ → Bool) :
    vertexCount P = vertexCount (P.map (List.map (signedDartEquiv e flip))) := by
  let r := signedDartEquiv e flip
  let Q := P.map (List.map r)
  have hcQ : ∀ a b, corner Q a b → Quotient.mk (vertexSetoid Q) a = Quotient.mk _ b :=
    fun _ _ h ↦ Quotient.sound (Relation.EqvGen.rel _ _ h)
  have hcP : ∀ a b, corner P a b →
      Quotient.mk (vertexSetoid P) (r.symm (r a)) = Quotient.mk _ (r.symm (r b)) := by
    intro a b hab
    simpa using (Quotient.sound (Relation.EqvGen.rel _ _ hab) :
      Quotient.mk (vertexSetoid P) a = Quotient.mk _ b)
  have hmem (a : Dart) : r a ∈ vertexDarts Q ↔ a ∈ vertexDarts P := by
    simp only [vertexDarts_mem, Q, labels, occurrences, ← List.map_flatten,
      List.map_map, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨b, hb, he⟩
      exact ⟨b, hb, e.injective he⟩
    · rintro ⟨b, hb, he⟩
      exact ⟨b, hb, congrArg e he⟩
  apply vertexCount_transport r r.symm
  · intro a b hab
    exact Quotient.exact ((corner_compatible_map _ r (signedDartEquiv_inverse e flip) P).mp hcQ a b hab)
  · intro a b hab
    exact Quotient.exact ((corner_compatible_map (fun a ↦ Quotient.mk (vertexSetoid P) (r.symm a)) r (signedDartEquiv_inverse e flip) P).mpr hcP a b hab)
  · exact fun a ha ↦ (hmem a).mpr ha
  · intro a ha
    apply (hmem (r.symm a)).mp
    simpa using ha
  · intro a ha
    simp only [Equiv.symm_apply_apply]
    exact Relation.EqvGen.refl a
  · intro a ha
    simp only [Equiv.apply_symm_apply]
    exact Relation.EqvGen.refl a

private theorem vertexCount_rename {P Q : Presentation} (e : ℕ ≃ ℕ) (flip : ℕ → Bool)
    (f : Fin P.length ≃ Fin Q.length)
    (hr : ∀ i, List.IsRotated
      ((P.get i).map fun d ↦ (e d.1, if flip d.1 then !d.2 else d.2)) (Q.get (f i))) :
    vertexCount P = vertexCount Q := by
  rw [vertexCount_signed_map P e flip]
  apply vertexCount_reindexed
  let r := signedDartEquiv e flip
  refine ⟨(finCongr (List.length_map (List.map r) (as := P))).trans f, ?_⟩
  intro i
  change List.IsRotated ((P.map (List.map r)).get i)
    (Q.get (f ⟨i.val, by simpa using i.isLt⟩))
  simp only [List.get_eq_getElem, List.getElem_map]
  exact hr ⟨i.val, by simpa using i.isLt⟩

private theorem chain_repeat_start {A : Type*} (R : A → A → Prop) (a : A) (U V : List A) :
    List.IsChain R ((a :: U) ++ V ++ [a]) ↔
      List.IsChain R ((a :: U) ++ V ++ (a :: U)) := by
  rw [List.isChain_split (l₁ := (a :: U) ++ V) (c := a) (l₂ := U)]
  exact ⟨fun h ↦ ⟨h, h.left_of_append.left_of_append⟩, fun h ↦ h.1⟩

private def splitTerminal (a b c : ℕ) (d : Dart) : Dart :=
  if d.1 = a then if d.2 then (c, true) else (b, false) else d

private def splitInitial (a b c : ℕ) (d : Dart) : Dart :=
  if d.1 = a then if d.2 then (b, true) else (c, false) else d

private theorem splitDart_endpoints (a b c : ℕ) (d : Dart) :
    (splitDart a b c d).head? = some (splitInitial a b c d) ∧
    (splitDart a b c d).getLast? = some (splitTerminal a b c d) ∧
    inverse (splitInitial a b c d) = splitTerminal a b c (inverse d) := by
  obtain ⟨i, s⟩ := d
  by_cases hi : i = a <;> cases s <;>
    simp [splitDart, splitInitial, splitTerminal, inverse, hi]

private theorem splitDart_chain {A : Type*} (f : Dart → A) (a b c : ℕ) (d : Dart) :
    List.IsChain (fun x y ↦ f x = f (inverse y)) (splitDart a b c d) ↔
      (d.1 = a → f (b, true) = f (c, false)) := by
  obtain ⟨i, s⟩ := d
  by_cases hi : i = a <;> cases s <;>
    simp [splitDart, inverse, hi, eq_comm]

private theorem corner_compatible_split_word {A : Type*} (f : Dart → A)
    (a b c : ℕ) (W : Word) :
    (∀ x y, corner [W.flatMap (splitDart a b c)] x y → f x = f y) ↔
      (∀ x y, corner [W] x y → f (splitTerminal a b c x) = f (splitTerminal a b c y)) ∧
      (∀ d ∈ W, d.1 = a → f (b, true) = f (c, false)) := by
  cases W with
  | nil => simp [corner]
  | cons z W =>
    have hn (d : Dart) : splitDart a b c d ≠ [] := by
      have hh := splitDart_length a b c d
      intro he
      rw [he, List.length_nil] at hh
      omega
    obtain ⟨u, U, hu⟩ := List.exists_cons_of_ne_nil (hn z)
    have hcycle : (∀ x y, corner [(z :: W).flatMap (splitDart a b c)] x y → f x = f y) ↔
        List.IsChain (fun x y ↦ f x = f (inverse y))
          (((z :: W) ++ [z]).flatMap (splitDart a b c)) := by
      rw [List.flatMap_cons, hu, List.cons_append, corner_compatible_chain]
      rw [show ((u :: (U ++ W.flatMap (splitDart a b c))) ++ [u]) =
        (u :: U) ++ W.flatMap (splitDart a b c) ++ [u] by simp]
      rw [chain_repeat_start]
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, hu]
    rw [hcycle, List.flatMap_def, List.isChain_flatten]
    · simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        List.isChain_map]
      have hbridge (x y : Dart) :
          (∀ u ∈ (splitDart a b c x).getLast?, ∀ v ∈ (splitDart a b c y).head?,
            f u = f (inverse v)) ↔
          f (splitTerminal a b c x) = f (splitTerminal a b c (inverse y)) := by
        rw [(splitDart_endpoints a b c x).2.1, (splitDart_endpoints a b c y).1]
        simp only [Option.mem_some_iff, forall_eq', (splitDart_endpoints a b c y).2.2]
      simp only [hbridge, splitDart_chain, List.mem_append, List.mem_cons,
        or_imp, forall_and, forall_eq]
      rw [corner_compatible_chain]
      tauto
    · intro he
      obtain ⟨d, hd, he⟩ := List.mem_map.mp he
      exact hn d he

private theorem corner_compatible_subdivide {A : Type*} (f : Dart → A)
    (P : Presentation) (a b c : ℕ) (ha : a ∈ labels P) :
    (∀ x y, corner (subdivideEdge P a b c) x y → f x = f y) ↔
      (∀ x y, corner P x y → f (splitTerminal a b c x) = f (splitTerminal a b c y)) ∧
      f (b, true) = f (c, false) := by
  rw [corner_compatible_words (subdivideEdge P a b c), corner_compatible_words P]
  change (∀ W ∈ P.map (List.flatMap (splitDart a b c)), _) ↔ _
  constructor
  · intro h
    have hW W (hW : W ∈ P) := (corner_compatible_split_word f a b c W).mp
      (h _ (List.mem_map.mpr ⟨W, hW, rfl⟩))
    refine ⟨fun W hw ↦ (hW W hw).1, ?_⟩
    simp only [labels, occurrences, List.mem_toFinset, List.mem_map] at ha
    obtain ⟨d, hd, he⟩ := ha
    obtain ⟨W, hWP, hdW⟩ := List.mem_flatten.mp hd
    exact (hW W hWP).2 d hdW he
  · rintro ⟨h, hm⟩ W hW
    obtain ⟨Z, hZ, he⟩ := List.mem_map.mp hW
    subst W
    exact (corner_compatible_split_word f a b c Z).mpr ⟨h Z hZ, fun _ _ _ ↦ hm⟩

private theorem vertexCount_option_classifier (P Q : Presentation)
    (f : Dart → Option (Quotient (vertexSetoid P)))
    (hf : ∀ a b, corner Q a b → f a = f b)
    (hi : ∀ a ∈ vertexDarts Q, ∀ b ∈ vertexDarts Q, f a = f b → sameVertex Q a b)
    (hs : ∀ x, x ∈ insert none ((vertexClasses P).image some) ↔
      ∃ a ∈ vertexDarts Q, f a = x) : vertexCount Q = vertexCount P + 1 := by
  let F : Quotient (vertexSetoid Q) → Option (Quotient (vertexSetoid P)) :=
    Quotient.lift f (fun _ _ h ↦ sameVertex_map_eq f hf h)
  have hmap : (vertexClasses Q).image F = insert none ((vertexClasses P).image some) := by
    ext x
    rw [hs]
    constructor
    · intro hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact Finset.mem_image.mpr ⟨Quotient.mk _ a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, rfl⟩
  have hinj : Set.InjOn F (vertexClasses Q) := by
    intro x hx y hy he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact Quotient.sound (hi a ha b hb he)
  have hcard := Finset.card_image_of_injOn hinj
  rw [hmap, Finset.card_insert_of_notMem (by simp),
    Finset.card_image_of_injective _ (Option.some_injective _)] at hcard
  exact hcard.symm

private theorem edge_subdivision_vertexCount (P : Presentation) (a b c : ℕ)
    (ha : a ∈ labels P) (hb : b ∉ labels P) (hc : c ∉ labels P) (hbc : b ≠ c) :
    vertexCount (subdivideEdge P a b c) = vertexCount P + 1 := by
  let Q := subdivideEdge P a b c
  let emb := splitTerminal a b c
  let collapse : Dart → Dart := fun x ↦
    if x.1 = b then (a, false) else if x.1 = c then (a, true) else x
  let mid : Dart → Prop := fun x ↦ x = (b, true) ∨ x = (c, false)
  let πP : Dart → Quotient (vertexSetoid P) := Quotient.mk _
  let πQ : Dart → Quotient (vertexSetoid Q) := Quotient.mk _
  let f : Dart → Option (Quotient (vertexSetoid P)) := fun x ↦
    if mid x then none else some (πP (collapse x))
  have hab : a ≠ b := fun h ↦ hb (h ▸ ha)
  have hac : a ≠ c := fun h ↦ hc (h ▸ ha)
  have hlabels (k : ℕ) : k ∈ labels Q ↔ k = b ∨ k = c ∨ (k ∈ labels P ∧ k ≠ a) := by
    rw [← labelMultiplicity_pos, labelMultiplicity_edge P a b c ha hb hc hbc]
    have hp := (labelMultiplicity_pos P a).mpr ha
    by_cases hkb : k = b <;> by_cases hkc : k = c <;> by_cases hka : k = a <;>
      simp_all [labelMultiplicity_pos]
  have hem (x : Dart) (hx : x ∈ vertexDarts P) : emb x ∈ vertexDarts Q := by
    rw [vertexDarts_mem] at hx ⊢
    rw [hlabels]
    obtain ⟨k, s⟩ := x
    by_cases hk : k = a <;> cases s <;> simp_all [emb, splitTerminal]
  have hfe (x : Dart) (hx : x ∈ vertexDarts P) : f (emb x) = some (πP x) := by
    have hx' := (vertexDarts_mem P x).mp hx
    have hxb : x.1 ≠ b := fun h ↦ hb (h ▸ hx')
    have hxc : x.1 ≠ c := fun h ↦ hc (h ▸ hx')
    obtain ⟨k, s⟩ := x
    by_cases hk : k = a <;> cases s <;>
      simp_all [f, mid, collapse, emb, splitTerminal, Ne.symm hbc]
  have hcollapse_mem (x : Dart) (hx : x ∈ vertexDarts Q) : collapse x ∈ vertexDarts P := by
    rw [vertexDarts_mem] at hx ⊢
    rcases (hlabels x.1).mp hx with h | h | h
    · simp [collapse, h, ha]
    · simp [collapse, h, ha, Ne.symm hbc]
    · by_cases hxb : x.1 = b
      · simp [collapse, hxb, ha]
      · by_cases hxc : x.1 = c
        · simp [collapse, hxc, ha, Ne.symm hbc]
        · simpa [collapse, hxb, hxc] using h.1
  have hemb_collapse (x : Dart) (hx : x ∈ vertexDarts Q) (hm : ¬ mid x) : emb (collapse x) = x := by
    have hx' := (hlabels x.1).mp ((vertexDarts_mem Q x).mp hx)
    obtain ⟨k, s⟩ := x
    by_cases hkb : k = b <;> by_cases hkc : k = c <;> cases s <;>
      simp_all [emb, collapse, splitTerminal, mid, Ne.symm hab, Ne.symm hac]
  have hπQ : ∀ x y, corner Q x y → πQ x = πQ y :=
    fun _ _ h ↦ Quotient.sound (Relation.EqvGen.rel _ _ h)
  have hQdata := (corner_compatible_subdivide πQ P a b c ha).mp hπQ
  have hf : ∀ x y, corner Q x y → f x = f y := by
    apply (corner_compatible_subdivide f P a b c ha).mpr
    refine ⟨?_, ?_⟩
    · intro x y hxy
      rw [hfe x ((vertexDarts_mem P x).mpr (corner_labels hxy).1),
        hfe y ((vertexDarts_mem P y).mpr (corner_labels hxy).2)]
      exact congrArg some (Quotient.sound (Relation.EqvGen.rel _ _ hxy))
    · simp [f, mid]
  have hmid (x : Dart) (hm : mid x) : πQ x = πQ (b, true) := by
    rcases hm with rfl | rfl
    · rfl
    · exact hQdata.2.symm
  have hi : ∀ x ∈ vertexDarts Q, ∀ y ∈ vertexDarts Q, f x = f y → sameVertex Q x y := by
    intro x hx y hy hxy
    by_cases hmx : mid x
    · by_cases hmy : mid y
      · exact Quotient.exact ((hmid x hmx).trans (hmid y hmy).symm)
      · simp [f, hmx, hmy] at hxy
    · by_cases hmy : mid y
      · simp [f, hmx, hmy] at hxy
      · have he : πP (collapse x) = πP (collapse y) := by simpa [f, hmx, hmy] using hxy
        have hrel : sameVertex P (collapse x) (collapse y) := Quotient.exact he
        have he' := sameVertex_map_eq (πQ ∘ emb) hQdata.1 hrel
        simp only [Function.comp_def, hemb_collapse x hx hmx, hemb_collapse y hy hmy] at he'
        exact Quotient.exact he'
  apply vertexCount_option_classifier P Q f hf hi
  intro z
  constructor
  · intro hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · refine ⟨(b, true), ?_, ?_⟩
      · exact (vertexDarts_mem Q _).mpr ((hlabels b).mpr (Or.inl rfl))
      · simp [f, mid]
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      exact ⟨emb x, hem x hx, hfe x hx⟩
  · rintro ⟨x, hx, rfl⟩
    by_cases hm : mid x
    · simp [f, hm]
    · rw [show f x = some (πP (collapse x)) by simp [f, hm]]
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨πP (collapse x),
        Finset.mem_image.mpr ⟨collapse x, hcollapse_mem x hx, rfl⟩, rfl⟩)

private def presentationEuler (P : Presentation) : ℤ :=
  (vertexCount P : ℤ) - (labels P).card + P.length

private theorem labels_subdivide (P : Presentation) (a b c : ℕ)
    (ha : a ∈ labels P) (hb : b ∉ labels P) (hc : c ∉ labels P) (hbc : b ≠ c) :
    labels (subdivideEdge P a b c) = insert b (insert c ((labels P).erase a)) := by
  ext k
  rw [← labelMultiplicity_pos, labelMultiplicity_edge P a b c ha hb hc hbc]
  have hp := (labelMultiplicity_pos P a).mpr ha
  by_cases hkb : k = b <;> by_cases hkc : k = c <;> by_cases hka : k = a <;>
    simp_all [labelMultiplicity_pos, and_comm]

private theorem presentationEuler_edge (P : Presentation) (a b c : ℕ)
    (ha : a ∈ labels P) (hb : b ∉ labels P) (hc : c ∉ labels P) (hbc : b ≠ c) :
    presentationEuler P = presentationEuler (subdivideEdge P a b c) := by
  have he : (labels (subdivideEdge P a b c)).card = (labels P).card + 1 := by
    rw [labels_subdivide P a b c ha hb hc hbc,
      Finset.card_insert_of_notMem (by simp [hbc, hb]),
      Finset.card_insert_of_notMem (by simp [hc]), Finset.card_erase_of_mem ha]
    have hp := Finset.card_pos.mpr ⟨a, ha⟩
    omega
  unfold presentationEuler
  rw [edge_subdivision_vertexCount P a b c ha hb hc hbc, he]
  simp only [subdivideEdge, List.length_map, Nat.cast_add, Nat.cast_one]
  ring

private theorem presentationEuler_face (L R : Presentation) (U V : Word) (d : ℕ)
    (hU : U ≠ []) (hV : V ≠ []) (hd : d ∉ labels (L ++ [U ++ V] ++ R)) :
    presentationEuler (L ++ [U ++ V] ++ R) =
      presentationEuler (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R) := by
  have hl : labels (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R) =
      insert d (labels (L ++ [U ++ V] ++ R)) := by
    ext a
    simp only [labels, occurrences, List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.map_append, List.map_cons, List.map_nil,
      List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Finset.mem_insert]
    tauto
  simp only [presentationEuler, hl, Finset.card_insert_of_notMem hd,
    ← face_subdivision_vertexCount L R U V d hU hV hd, List.length_append,
    List.length_cons, List.length_nil, Nat.cast_add, Nat.cast_one, Nat.cast_zero]
  ring

private theorem presentationEuler_reindexed {P Q : Presentation} (h : Reindexed P Q) :
    presentationEuler P = presentationEuler Q := by
  have hl : labels P = labels Q := by
    ext a
    rw [← labelMultiplicity_pos, ← labelMultiplicity_pos, labelMultiplicity_reindexed h]
  have hlen : P.length = Q.length := by
    obtain ⟨e, he⟩ := h
    simpa using Fintype.card_congr e
  simp only [presentationEuler, vertexCount_reindexed h, hl, hlen]

private theorem presentationEuler_rename {P Q : Presentation} (e : ℕ ≃ ℕ) (flip : ℕ → Bool)
    (f : Fin P.length ≃ Fin Q.length)
    (hr : ∀ i, List.IsRotated
      ((P.get i).map fun d ↦ (e d.1, if flip d.1 then !d.2 else d.2)) (Q.get (f i))) :
    presentationEuler P = presentationEuler Q := by
  have hl : (labels P).image e = labels Q := by
    ext a
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [← labelMultiplicity_pos, ← labelMultiplicity_rename e flip f hr]
      exact (labelMultiplicity_pos P k).mpr hk
    · intro ha
      refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
      rw [← labelMultiplicity_pos, labelMultiplicity_rename e flip f hr, e.apply_symm_apply]
      exact (labelMultiplicity_pos Q a).mpr ha
  have hcard : (labels P).card = (labels Q).card := by
    rw [← hl, Finset.card_image_of_injective _ e.injective]
  have hlen : P.length = Q.length := by simpa using Fintype.card_congr f
  simp only [presentationEuler, vertexCount_rename e flip f hr, hcard, hlen]

private theorem Elementary.euler {P Q : Presentation} (h : Elementary P Q) :
    presentationEuler P = presentationEuler Q := by
  induction h with
  | edge P a b c ha hb hc hbc => exact presentationEuler_edge P a b c ha hb hc hbc
  | face L R U V d hU hV hd => exact presentationEuler_face L R U V d hU hV hd
  | inverse h ih => exact ih.symm
  | reindex h => exact presentationEuler_reindexed h
  | rename e flip f hr => exact presentationEuler_rename e flip f hr

private theorem RealizedSequence.euler {P Q : Presentation} (s : RealizedSequence P Q) :
    presentationEuler P = presentationEuler Q := by
  induction s with
  | nil => rfl
  | cons h H hH s ih => exact h.euler.trans ih

private def blockVertexValues {A : Type*} (f : Dart → A) (base : A) (q : ReductionBlock) : Prop :=
  if q.isHandle then
    f q.a = base ∧ f q.b = base ∧ f (inverse q.a) = base ∧ f (inverse q.b) = base
  else f (inverse q.a) = base ∧ f q.a = f q.b ∧ f (inverse q.b) = f q.b

private theorem blocks_chain_values {A : Type*} (f : Dart → A) (B : List ReductionBlock)
    (z w : Dart) :
    List.IsChain (fun d e ↦ f d = f (inverse e)) (z :: (blocksWord B ++ [w])) ↔
      f z = f (inverse w) ∧ ∀ q ∈ B, blockVertexValues f (f (inverse w)) q := by
  induction B generalizing z with
  | nil => simp [blocksWord]
  | cons q B ih =>
    cases hq : q.isHandle
    · simp only [blocksWord, List.flatMap_cons, ReductionBlock.word, hq, Bool.false_eq_true,
        ite_false, List.cons_append, List.nil_append, List.isChain_cons_cons]
      change (f z = f (inverse q.a) ∧ f q.a = f (inverse q.b) ∧
        f q.b = f (inverse (inverse q.a)) ∧
        List.IsChain (fun d e ↦ f d = f (inverse e)) (inverse q.a :: (blocksWord B ++ [w]))) ↔ _
      rw [ih]
      simp only [inverse, Bool.not_not, List.mem_cons, forall_eq_or_imp, blockVertexValues, hq,
        Bool.false_eq_true, ite_false]
      constructor
      · rintro ⟨hz, hab, hba, ha, hB⟩
        exact ⟨hz.trans ha, ⟨ha, hba.symm, hab.symm.trans hba.symm⟩, hB⟩
      · rintro ⟨hz, ⟨ha, hab, hba⟩, hB⟩
        exact ⟨hz.trans ha.symm, hab.trans hba.symm, hab.symm, ha, hB⟩
    · simp only [blocksWord, List.flatMap_cons, ReductionBlock.word, hq, ite_true,
        List.cons_append, List.nil_append, List.isChain_cons_cons]
      change (f z = f (inverse q.a) ∧ f q.a = f (inverse q.b) ∧
        f q.b = f (inverse (inverse q.a)) ∧ f (inverse q.a) = f (inverse (inverse q.b)) ∧
        List.IsChain (fun d e ↦ f d = f (inverse e)) (inverse q.b :: (blocksWord B ++ [w]))) ↔ _
      rw [ih]
      simp only [inverse, Bool.not_not, List.mem_cons, forall_eq_or_imp, blockVertexValues, hq,
        ite_true]
      constructor
      · rintro ⟨hz, hab, hba, hab', hb, hB⟩
        have ha := hab.trans hb
        have hbb := hba.trans ha
        have haa := hab'.trans hbb
        exact ⟨hz.trans haa, ⟨ha, hbb, haa, hb⟩, hB⟩
      · rintro ⟨hz, ⟨ha, hb, ha', hb'⟩, hB⟩
        exact ⟨hz.trans ha'.symm, ha.trans hb'.symm, hb.trans ha.symm,
          ha'.trans hb.symm, hb', hB⟩

private theorem blocks_corner_values {A : Type*} (f : Dart → A)
    (q : ReductionBlock) (B : List ReductionBlock) :
    (∀ d e, corner [blocksWord (q :: B)] d e → f d = f e) ↔
      ∀ r ∈ q :: B, blockVertexValues f (f (inverse q.a)) r := by
  have hw : ∃ W, blocksWord (q :: B) = q.a :: W := by
    cases h : q.isHandle <;> simp [blocksWord, ReductionBlock.word, h]
  obtain ⟨W, hW⟩ := hw
  have hh := blocks_chain_values f (q :: B) (inverse q.a) q.a
  rw [hW, List.cons_append, List.isChain_cons_cons] at hh
  rw [hW, corner_compatible_chain]
  simpa only [List.cons_append, eq_self, true_and] using hh

private def standardBlocks (g b : ℕ) : List ReductionBlock :=
  ((List.range g).map fun i ↦ ⟨true, (2*i, true), (2*i+1, true), by simp⟩) ++
  ((List.range b).map fun j ↦ ⟨false, (2*g+2*j, true), (2*g+2*j+1, true), by simp⟩)

private theorem standardBlocks_word (g b : ℕ) : blocksWord (standardBlocks g b) = normalWord g b := by
  simp [blocksWord, standardBlocks, normalWord, List.flatMap_append, List.flatMap_map,
    ReductionBlock.word, inverse]

private theorem blocks_corner_values_exists {A : Type*} (f : Dart → A)
    (B : List ReductionBlock) (hB : B ≠ []) :
    (∀ d e, corner [blocksWord B] d e → f d = f e) ↔
      ∃ base, ∀ r ∈ B, blockVertexValues f base r := by
  obtain ⟨q, B, rfl⟩ := List.exists_cons_of_ne_nil hB
  rw [blocks_corner_values]
  constructor
  · exact fun h ↦ ⟨f (inverse q.a), h⟩
  · rintro ⟨base, h⟩
    have hq := h q (by simp)
    have he : f (inverse q.a) = base := by
      cases hh : q.isHandle <;> simp only [blockVertexValues, hh, Bool.false_eq_true,
        ite_false, ite_true] at hq
      · exact hq.1
      · exact hq.2.2.1
    rwa [he]

private theorem normal_corner_values {A : Type*} (f : Dart → A) (g b : ℕ) (hb : 0 < b) :
    (∀ d e, corner [normalWord g b] d e → f d = f e) ↔
      ∃ base,
        (∀ i < g, f (2*i, true) = base ∧ f (2*i+1, true) = base ∧
          f (2*i, false) = base ∧ f (2*i+1, false) = base) ∧
        (∀ j < b, f (2*g+2*j, false) = base ∧
          f (2*g+2*j, true) = f (2*g+2*j+1, true) ∧
          f (2*g+2*j+1, false) = f (2*g+2*j+1, true)) := by
  rw [← standardBlocks_word]
  have hne : standardBlocks g b ≠ [] := by
    simp [standardBlocks, List.append_eq_nil_iff, List.map_eq_nil_iff, List.range_eq_nil, Nat.ne_of_gt hb]
  rw [blocks_corner_values_exists f _ hne]
  simp only [standardBlocks, List.mem_append, or_imp, forall_and,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    List.mem_range, blockVertexValues, ite_true, Bool.false_eq_true, ite_false, inverse,
    Bool.not_true]

private def normalVertexClassifier (g b : ℕ) (d : Dart) : Option (Fin b) :=
  if h : 2*g ≤ d.1 ∧ d.1 < 2*g+2*b then
    if d.1 % 2 = 1 ∨ d.2 = true then
      some ⟨(d.1 - 2*g) / 2, by omega⟩
    else none
  else none

private theorem normalVertexClassifier_handle (g b i : ℕ) (hi : i < g) (s : Bool) :
    normalVertexClassifier g b (2*i, s) = none ∧
    normalVertexClassifier g b (2*i+1, s) = none := by
  have h1 : ¬ 2*g ≤ 2*i := by omega
  have h2 : ¬ 2*g ≤ 2*i+1 := by omega
  simp [normalVertexClassifier, h1, h2]

private theorem normalVertexClassifier_loop (g b : ℕ) (j : Fin b) :
    normalVertexClassifier g b (2*g+2*j.val, false) = none ∧
    normalVertexClassifier g b (2*g+2*j.val, true) = some j ∧
    normalVertexClassifier g b (2*g+2*j.val+1, true) = some j ∧
    normalVertexClassifier g b (2*g+2*j.val+1, false) = some j := by
  have hj := j.isLt
  have h0 : 2*g ≤ 2*g+2*j.val ∧ 2*g+2*j.val < 2*g+2*b := by omega
  have h1 : 2*g ≤ 2*g+2*j.val+1 ∧ 2*g+2*j.val+1 < 2*g+2*b := by omega
  have he : (2*g+2*j.val) % 2 = 0 := by omega
  have ho : (2*g+2*j.val+1) % 2 = 1 := by omega
  simp only [normalVertexClassifier, h0, h1, dite_true, he, ho, zero_ne_one,
    Bool.false_eq_true, or_self, ite_false, or_true, ite_true, true_or, and_self, true_and]
  constructor <;> apply congrArg some <;> apply Fin.ext <;> simp; omega

private theorem normalWord_vertexCount (g b : ℕ) (hb : 0 < b) :
    vertexCount [normalWord g b] = b + 1 := by
  let P : Presentation := [normalWord g b]
  let f := normalVertexClassifier g b
  let π : Dart → Quotient (vertexSetoid P) := Quotient.mk _
  let repr : Option (Fin b) → Dart := fun x ↦ match x with
    | none => (2*g, false)
    | some j => (2*g+2*j.val+1, true)
  have hπ : ∀ d e, corner P d e → π d = π e :=
    fun _ _ h ↦ Quotient.sound (Relation.EqvGen.rel _ _ h)
  obtain ⟨base, hhandles, hloops⟩ := (normal_corner_values π g b hb).mp hπ
  have hbase : π (2*g, false) = base := by simpa using (hloops 0 hb).1
  have hm (d : Dart) : d ∈ vertexDarts P ↔ d.1 < 2*g+2*b := by
    rw [vertexDarts_mem, normalWord_labels]
    exact Finset.mem_range
  have hf : ∀ d e, corner P d e → f d = f e := by
    apply (normal_corner_values f g b hb).mpr
    refine ⟨none, ?_, ?_⟩
    · intro i hi
      exact ⟨(normalVertexClassifier_handle g b i hi true).1,
        (normalVertexClassifier_handle g b i hi true).2,
        (normalVertexClassifier_handle g b i hi false).1,
        (normalVertexClassifier_handle g b i hi false).2⟩
    · intro j hj
      have hh := normalVertexClassifier_loop g b ⟨j, hj⟩
      exact ⟨hh.1, hh.2.1.trans hh.2.2.1.symm, hh.2.2.2.trans hh.2.2.1.symm⟩
  have hclass : ∀ d ∈ vertexDarts P, π d = π (repr (f d)) := by
    rintro ⟨k, s⟩ hd
    have hk : k < 2*g+2*b := (hm _).mp hd
    dsimp only [f]
    by_cases hkg : k < 2*g
    · let i := k / 2
      have hi : i < g := by dsimp [i]; omega
      have he : k = 2*i ∨ k = 2*i+1 := by dsimp [i]; omega
      rcases he with he | he <;> rw [he] <;> cases s
      · rw [(normalVertexClassifier_handle g b i hi false).1]
        exact (hhandles i hi).2.2.1.trans hbase.symm
      · rw [(normalVertexClassifier_handle g b i hi true).1]
        exact (hhandles i hi).1.trans hbase.symm
      · rw [(normalVertexClassifier_handle g b i hi false).2]
        exact (hhandles i hi).2.2.2.trans hbase.symm
      · rw [(normalVertexClassifier_handle g b i hi true).2]
        exact (hhandles i hi).2.1.trans hbase.symm
    · let j : Fin b := ⟨(k-2*g)/2, by omega⟩
      have he : k = 2*g+2*j.val ∨ k = 2*g+2*j.val+1 := by dsimp [j]; omega
      rcases he with he | he
      · rw [he]
        cases s
        · rw [(normalVertexClassifier_loop g b j).1]
          exact (hloops j.val j.isLt).1.trans hbase.symm
        · rw [(normalVertexClassifier_loop g b j).2.1]
          exact (hloops j.val j.isLt).2.1
      · rw [he]
        cases s
        · rw [(normalVertexClassifier_loop g b j).2.2.2]
          exact (hloops j.val j.isLt).2.2
        · rw [(normalVertexClassifier_loop g b j).2.2.1]
  have hi : ∀ d ∈ vertexDarts P, ∀ e ∈ vertexDarts P, f d = f e → sameVertex P d e := by
    intro d hd e he hde
    exact Quotient.exact ((hclass d hd).trans ((congrArg (π ∘ repr) hde).trans (hclass e he).symm))
  have hs : ∀ x, ∃ d ∈ vertexDarts P, f d = x := by
    intro x
    cases x with
    | none =>
      refine ⟨(2*g, false), (hm _).mpr (by simp; omega), ?_⟩
      simpa [f] using (normalVertexClassifier_loop g b ⟨0, hb⟩).1
    | some j =>
      exact ⟨(2*g+2*j.val+1, true), (hm _).mpr (by have := j.isLt; simp; omega),
        (normalVertexClassifier_loop g b j).2.2.1⟩
  simpa using vertexCount_of_classifier P f hf hi hs

private theorem normalWord_presentationEuler (g b : ℕ) (hb : 0 < b) :
    presentationEuler [normalWord g b] = 2 - 2*(g : ℤ) - b := by
  rw [presentationEuler, normalWord_vertexCount g b hb, normalWord_labels_card]
  simp only [List.length_singleton, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

private def dartTerminal (d : Dart) : ℕ := if d.2 then (Nat.unpair d.1).2 else (Nat.unpair d.1).1

private theorem dartTerminal_edgeDart {N : ℕ} (u v : Fin N) :
    dartTerminal (edgeDart u v) = v.val ∧ dartTerminal (inverse (edgeDart u v)) = u.val := by
  by_cases h : u < v
  · simp [dartTerminal, edgeDart, edgeLabel, inverse, h, Nat.unpair_pair] ; exact h.le
  · have h' : v ≤ u := le_of_not_gt h
    simp [dartTerminal, edgeDart, edgeLabel, inverse, h, Nat.unpair_pair] ; exact h'

private theorem edgeDart_inverse {N : ℕ} {u v : Fin N} (h : u ≠ v) :
    inverse (edgeDart u v) = edgeDart v u := by
  rcases lt_or_gt_of_ne h with h | h <;>
    simp [inverse, edgeDart, edgeLabel_comm, h, not_lt.mpr h.le]

private theorem original_dart_representative {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) {d : Dart}
    (hd : d ∈ vertexDarts (trianglePresentation K o)) :
    ∃ u v : Fin N, u ≠ v ∧ ({u,v} : Finset (Fin N)) ∈ K.faces ∧ d = edgeDart u v := by
  obtain ⟨u, v, huv, he, hl⟩ := triangle_label_endpoints K o ((vertexDarts_mem _ d).mp hd)
  have hsign : d = edgeDart u v ∨ d = edgeDart v u := by
    apply Or.imp (fun h ↦ Prod.ext hl h) (fun h ↦ Prod.ext (hl.trans (edgeLabel_comm u v)) h)
    change d.2 = decide (u < v) ∨ d.2 = decide (v < u)
    by_cases h : u < v
    · have h' : ¬ v < u := not_lt.mpr h.le
      cases d.2 <;> simp [h, h']
    · have h' : v < u := lt_of_le_of_ne (le_of_not_gt h) huv.symm
      cases d.2 <;> simp [h, h']
  rcases hsign with h | h
  · exact ⟨u, v, huv, he, h⟩
  · exact ⟨v, u, huv.symm, by simpa [Finset.pair_comm] using he, h⟩

private theorem original_corner_terminal {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) {a b : Dart}
    (h : corner (trianglePresentation K o) a b) : dartTerminal a = dartTerminal b := by
  obtain ⟨W, hW, j, i, ha, hb⟩ := corner_iff_word.mp h
  have hj : j = 0 := Fin.eq_zero j
  subst j
  have hw : ∃ s : Triangle K, W = triangleWord s (o s) := by
    simp only [trianglePresentation, List.mem_map] at hW
    obtain ⟨s, hs, he⟩ := hW
    exact ⟨_, he.symm⟩
  obtain ⟨s, rfl⟩ := hw
  subst a
  subst b
  change dartTerminal ((triangleWord s (o s)).get i) =
    dartTerminal (inverse ((triangleWord s (o s)).get (finRotate _ i)))
  obtain ⟨i, hi⟩ := i
  have hi3 : i < 3 := by simpa [triangleWord] using hi
  have he : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases he with rfl | rfl | rfl
  · exact (dartTerminal_edgeDart (o s 0).val (o s 1).val).1.trans
      (dartTerminal_edgeDart (o s 1).val (o s 2).val).2.symm
  · exact (dartTerminal_edgeDart (o s 1).val (o s 2).val).1.trans
      (dartTerminal_edgeDart (o s 2).val (o s 0).val).2.symm
  · exact (dartTerminal_edgeDart (o s 2).val (o s 0).val).1.trans
      (dartTerminal_edgeDart (o s 0).val (o s 1).val).2.symm

private theorem original_edge_label_mem {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (hpure : PureTwo K)
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) {u v : Fin N}
    (huv : u ≠ v) (he : ({u,v} : Finset (Fin N)) ∈ K.faces) :
    edgeLabel u v ∈ labels (trianglePresentation K o) := by
  obtain ⟨t, ht, hcard, hsub⟩ := hpure _ he
  let s : Triangle K := ⟨t, ht, hcard⟩
  obtain ⟨i, hi⟩ := triangle_pair_side s (o s) (hsub (by simp)) (hsub (by simp)) huv
  obtain ⟨j, hj⟩ := triangle_word_occurs K o s
  simp only [labels, List.mem_toFinset, List.mem_map]
  refine ⟨(triangleWord s (o s)).get i, ?_, hi⟩
  apply List.mem_flatten.mpr
  exact ⟨triangleWord s (o s), hj ▸ List.get_mem _ j, List.get_mem _ i⟩

private theorem original_triangle_corner_step {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) (s : Triangle K) (i : Fin 3) :
    sameVertex (trianglePresentation K o)
      (edgeDart (o s i).val (o s (finRotate 3 i)).val)
      (edgeDart (o s (finRotate 3 (finRotate 3 i))).val (o s (finRotate 3 i)).val) := by
  have hn : (o s (finRotate 3 i)).val ≠ (o s (finRotate 3 (finRotate 3 i))).val := by
    intro he
    have hn : ∀ j : Fin 3, j ≠ finRotate 3 j := by decide
    exact hn _ ((o s).injective (Subtype.ext he))
  rw [← edgeDart_inverse hn]
  apply Relation.EqvGen.rel
  apply corner_iff_word.mpr
  obtain ⟨j, hj⟩ := triangle_word_occurs K o s
  refine ⟨triangleWord s (o s), hj ▸ List.get_mem _ j, 0,
    ⟨i.val, by simp [triangleWord]⟩, ?_, ?_⟩
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl

private theorem original_triangle_incoming {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) (s : Triangle K)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    sameVertex (trianglePresentation K o)
      (edgeDart (o s i).val (o s j).val) (edgeDart (o s k).val (o s j).val) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> try contradiction
  all_goals first
    | exact original_triangle_corner_step K o s 0
    | exact original_triangle_corner_step K o s 1
    | exact original_triangle_corner_step K o s 2
    | exact Relation.EqvGen.symm _ _ (original_triangle_corner_step K o s 0)
    | exact Relation.EqvGen.symm _ _ (original_triangle_corner_step K o s 1)
    | exact Relation.EqvGen.symm _ _ (original_triangle_corner_step K o s 2)

private theorem original_link_incoming {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) {v a b : Fin N}
    (h : linkEdge K v a b) :
    sameVertex (trianglePresentation K o) (edgeDart a v) (edgeDart b v) := by
  obtain ⟨hab, hav, hbv, ht⟩ := h
  let s : Triangle K := ⟨{v,a,b}, ht, by simp [Ne.symm hav, Ne.symm hbv, hab]⟩
  let i := (o s).symm ⟨a, by simp [s]⟩
  let j := (o s).symm ⟨v, by simp [s]⟩
  let k := (o s).symm ⟨b, by simp [s]⟩
  have hij : i ≠ j := by
    intro h
    have he := congrArg (fun n ↦ (o s n).val) h
    exact hav (by simpa [i, j] using he)
  have hjk : j ≠ k := by
    intro h
    have he := congrArg (fun n ↦ (o s n).val) h
    exact hbv (by simpa [j, k] using he.symm)
  have hik : i ≠ k := by
    intro h
    have he := congrArg (fun n ↦ (o s n).val) h
    exact hab (by simpa [i, k] using he)
  simpa [i, j, k] using original_triangle_incoming K o s i j k hij hjk hik

private theorem chain_function_eq {A X : Type*} (f : X → A) (l : List X)
    (h : List.IsChain (fun x y ↦ f x = f y) l) {a b : X} (ha : a ∈ l) (hb : b ∈ l) :
    f a = f b := by
  have hm : List.IsChain (· = ·) (l.map f) := (List.isChain_map f).mpr h
  cases hl : l.map f with
  | nil =>
    have hmem := List.mem_map_of_mem (f := f) ha
    rw [hl] at hmem
    exact (List.not_mem_nil hmem).elim
  | cons c L =>
    rw [hl, List.isChain_cons_eq_iff_eq_replicate] at hm
    have hh (x : X) (hx : x ∈ l) : f x = c := by
      have hx' := List.mem_map_of_mem (f := f) hx
      rw [hl, hm] at hx'
      simp only [List.mem_cons, List.mem_replicate] at hx'
      rcases hx' with he | ⟨_, he⟩ <;> exact he
    exact (hh a ha).trans (hh b hb).symm

private theorem original_vertex_incoming {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (hlinks : SurfaceLinks K)
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) {v a b : Fin N}
    (hav : a ≠ v) (hbv : b ≠ v)
    (ha : ({v,a} : Finset (Fin N)) ∈ K.faces)
    (hb : ({v,b} : Finset (Fin N)) ∈ K.faces) :
    sameVertex (trianglePresentation K o) (edgeDart a v) (edgeDart b v) := by
  let π : Fin N → Quotient (vertexSetoid (trianglePresentation K o)) :=
    fun x ↦ Quotient.mk _ (edgeDart x v)
  obtain ⟨l, hnd, hmem, htype⟩ := hlinks v
  have hchain : List.IsChain (fun x y ↦ π x = π y) l := by
    rw [List.isChain_iff_getElem]
    intro i hi
    have hi' : i < l.length := by omega
    have hrel : linkEdge K v (l[i]) (l[i+1]) := by
      rcases htype with ⟨hlen, he⟩ | ⟨hlen, he⟩
      · apply (he _ _).mpr
        refine ⟨⟨i, hi'⟩, Or.inl ⟨rfl, ?_⟩⟩
        have hr : finRotate l.length ⟨i, hi'⟩ = ⟨i+1, hi⟩ := by
          apply Fin.ext
          simp only [finRotate_apply, Fin.val_add]
          change (i + (1 % l.length)) % l.length = i+1
          rw [Nat.mod_eq_of_lt (by omega : 1 < l.length), Nat.mod_eq_of_lt hi]
        rw [hr]
        rfl
      · apply (he _ _).mpr
        exact ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩
    exact Quotient.sound (original_link_incoming K o hrel)
  exact Quotient.exact (chain_function_eq π l hchain ((hmem a).mpr ⟨hav, ha⟩)
    ((hmem b).mpr ⟨hbv, hb⟩))

private theorem trianglePresentation_vertexCount {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (hpure : PureTwo K) (hlinks : SurfaceLinks K)
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) (v₀ : Fin N) :
    vertexCount (trianglePresentation K o) = N := by
  let P := trianglePresentation K o
  let f : Dart → Fin N := fun d ↦ if h : dartTerminal d < N then ⟨dartTerminal d, h⟩ else v₀
  have hf (u v : Fin N) : f (edgeDart u v) = v := by
    simp only [f, (dartTerminal_edgeDart u v).1, v.isLt, dite_true]
  have hcorner : ∀ a b, corner P a b → f a = f b := by
    intro a b hab
    have he := original_corner_terminal K o hab
    simp only [f, he]
  have hinj : ∀ a ∈ vertexDarts P, ∀ b ∈ vertexDarts P, f a = f b → sameVertex P a b := by
    intro a ha b hb he
    obtain ⟨u, v, huv, huvface, rfl⟩ := original_dart_representative K o ha
    obtain ⟨w, z, hwz, hwzface, rfl⟩ := original_dart_representative K o hb
    rw [hf, hf] at he
    subst z
    exact original_vertex_incoming K hlinks o huv hwz
      (by simpa [Finset.pair_comm] using huvface) (by simpa [Finset.pair_comm] using hwzface)
  have hsurj : ∀ v, ∃ d ∈ vertexDarts P, f d = v := by
    intro v
    obtain ⟨l, hnd, hmem, htype⟩ := hlinks v
    have hlen : 0 < l.length := by rcases htype with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    let u := l.get ⟨0, hlen⟩
    have hu := (hmem u).mp (List.get_mem _ _)
    refine ⟨edgeDart u v, ?_, hf u v⟩
    apply (vertexDarts_mem P _).mpr
    exact original_edge_label_mem K hpure o hu.1 (by simpa [Finset.pair_comm] using hu.2)
  simpa using vertexCount_of_classifier P f hcorner hinj hsurj

private theorem trianglePresentation_label_count {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (hpure : PureTwo K)
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) :
    (labels (trianglePresentation K o)).card = (simplices K 1).card := by
  let P := trianglePresentation K o
  choose U V hne hface hlabel using
    (fun k : ↥(labels P) ↦ triangle_label_endpoints K o k.property)
  apply Finset.card_bij (fun k hk ↦ ({U ⟨k,hk⟩, V ⟨k,hk⟩} : Finset (Fin N)))
  · intro k hk
    simp only [simplices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hface ⟨k,hk⟩, by simp [hne ⟨k,hk⟩]⟩
  · intro k hk l hl he
    have hs := congrArg (fun s : Finset (Fin N) ↦ (s : Set (Fin N))) he
    simp only [Finset.coe_pair, Set.pair_eq_pair_iff] at hs
    have hk' : k = edgeLabel (U ⟨k,hk⟩) (V ⟨k,hk⟩) := hlabel ⟨k,hk⟩
    have hl' : l = edgeLabel (U ⟨l,hl⟩) (V ⟨l,hl⟩) := hlabel ⟨l,hl⟩
    rw [hk', hl']
    rcases hs with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rw [hu, hv]
    · rw [hu, hv, edgeLabel_comm]
  · intro t ht
    have ht' : t ∈ K.faces ∧ t.card = 2 := by simpa [simplices] using ht
    obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp ht'.2
    have hk := original_edge_label_mem K hpure o huv ht'.1
    refine ⟨edgeLabel u v, hk, ?_⟩
    have he := edgeLabel_endpoint_pair (hne ⟨edgeLabel u v,hk⟩) huv
      (hlabel ⟨edgeLabel u v,hk⟩).symm
    rcases he with ⟨hu,hv⟩ | ⟨hu,hv⟩ <;> simp [hu,hv,Finset.pair_comm]

private theorem trianglePresentation_euler {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (hpure : PureTwo K) (hlinks : SurfaceLinks K)
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) (v₀ : Fin N) :
    presentationEuler (trianglePresentation K o) =
      ((simplices K 0).card : ℤ) - ((simplices K 1).card : ℤ) + ((simplices K 2).card : ℤ) := by
  rw [presentationEuler, trianglePresentation_vertexCount K hpure hlinks o v₀,
    trianglePresentation_label_count K hpure o, trianglePresentation_length_g9,
    simplices_zero_card_g9]

/-- Data package for a realized orientable polygon reduction.

Source: Gallier–Xu, Lemma 6.1 pp.92–95 and Theorem 6.1 p.96, with the
parameter-preserving realization and boundary bookkeeping of Proposition 3.2
p.31 and Note F.4 p.167. Bundling the witnesses keeps the parent theorem's
normal-form, realization, boundary and Euler conclusions in one atomic datum.
-/
structure PolygonReductionWitness {N b : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (H₀ : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o))
    (B : Fin b → List (Fin N)) where
  g : ℕ
  Q : Presentation
  e : ℕ ≃ ℕ
  flip : ℕ → Bool
  f : Fin Q.length ≃ Fin ([normalWord g b] : Presentation).length
  wordEq : ∀ k, ((Q.get k).map fun a ↦ (e a.1, if flip a.1 then !a.2 else a.2)) =
    ([normalWord g b] : Presentation).get (f k)
  sequence : RealizedSequence (trianglePresentation K o) Q
  sigma : Fin b ≃ Fin b
  boundaryEq : ∀ j : Fin b,
    (H₀.trans sequence.homeomorph) '' cycleCarrier (K := K) (B j) =
      edgeImage Q (e.symm (2 * g + 2 * (sigma j).val + 1))
  eulerEq : ((simplices K 0).card : ℤ) - ((simplices K 1).card : ℤ) +
      ((simplices K 2).card : ℤ) = (2 : ℤ) - 2 * (g : ℤ) - (b : ℤ)

structure PolygonReductionCore {N b : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (B : Fin b → List (Fin N)) where
  g : ℕ
  Q : Presentation
  e : ℕ ≃ ℕ
  flip : ℕ → Bool
  f : Fin Q.length ≃ Fin ([normalWord g b] : Presentation).length
  wordEq : ∀ k, ((Q.get k).map fun a ↦ (e a.1, if flip a.1 then !a.2 else a.2)) =
    ([normalWord g b] : Presentation).get (f k)

structure PolygonReductionWithSequence {N b : ℕ}
    {K : AbstractSimplicialComplex (Fin N)}
    {o : (s : Triangle K) → Fin 3 ≃ ↥s.val}
    {B : Fin b → List (Fin N)}
    (c : PolygonReductionCore K o B) where
  sequence : RealizedSequence (trianglePresentation K o) c.Q

structure PolygonReductionWithBoundary {N b : ℕ}
    {K : AbstractSimplicialComplex (Fin N)}
    {o : (s : Triangle K) → Fin 3 ≃ ↥s.val}
    {H₀ : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o)}
    {B : Fin b → List (Fin N)}
    (c : PolygonReductionCore K o B)
    (s : PolygonReductionWithSequence c) where
  sigma : Fin b ≃ Fin b
  boundaryEq : ∀ j : Fin b,
    (H₀.trans s.sequence.homeomorph) '' cycleCarrier (K := K) (B j) =
      edgeImage c.Q (c.e.symm (2 * c.g + 2 * (sigma j).val + 1))

/--
Source: Gallier–Xu normal words, pp.88–90. This compatibility constructor
retains the former core-only API: choose genus zero and the literal canonical
word, with identity label and face bijections. A core alone asserts no relation
to K. The actual reduction chooses its core and sequence jointly in
`polygon_reduction_sequence`.
-/
theorem polygon_reduction_core
    {N b : ℕ} (K : AbstractSimplicialComplex (Fin N)) (_hb : 1 ≤ b)
    (_hpure : PureTwo K) (_hconnected : IsConnected (carrier K))
    (_hincidence : ∀ e ∈ simplices K 1, incidence K e = 1 ∨ incidence K e = 2)
    (_hlinks : SurfaceLinks K) (B : Fin b → List (Fin N)) (_hboundary : BoundaryCycles K B)
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (_horiented : Oriented (trianglePresentation K o))
    (H₀ : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o))
    (_hH₀ : OriginalParameters K o H₀) :
    ∃ _c : PolygonReductionCore K o B, True := by
  refine ⟨{ g := 0
            Q := [normalWord 0 b]
            e := Equiv.refl ℕ
            flip := fun _ ↦ false
            f := Equiv.refl _
            wordEq := ?_ }, trivial⟩
  intro k
  simp

/--
Source: Gallier–Xu Definitions 6.2–6.3 pp.81–86 and Lemma 6.1 pp.92–95.
Merge faces by induction on their number, retaining an original unpaired
boundary side. Normalize the remaining oriented word by the finite anchored
reduction and append its signed relabeling. The boundary trace is preserved by
each move. Its two finite disjoint connected decompositions, by original cycles
and canonical loops, correspond bijectively, proving that the loop count is b.

Statement correction: the old theorem universally quantified over an arbitrary
core c, which only specifies a normal word. For a single triangular disk, the
core g=1, b=1 would demand a disk-to-punctured-torus reduction, contradicting
Euler counts 1 and -1. Choose c jointly with its sequence. The final witness
statement, all target definitions, and all downstream statements are unchanged.
-/
theorem polygon_reduction_sequence
    {N b : ℕ} (K : AbstractSimplicialComplex (Fin N)) (hb : 1 ≤ b)
    (_hpure : PureTwo K) (hconnected : IsConnected (carrier K))
    (_hincidence : ∀ e ∈ simplices K 1, incidence K e = 1 ∨ incidence K e = 2)
    (_hlinks : SurfaceLinks K) (B : Fin b → List (Fin N)) (hboundary : BoundaryCycles K B)
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (horiented : Oriented (trianglePresentation K o))
    (H₀ : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o))
    (hH₀ : OriginalParameters K o H₀) :
    ∃ c : PolygonReductionCore K o B, ∃ _s : PolygonReductionWithSequence c, True := by
  obtain ⟨g, b', hb', Q, ⟨s⟩, e, flip, he⟩ :=
    triangle_presentation_normal_form K hb hconnected B hboundary o horiented H₀
  have hword : ∀ k : Fin ([Q] : Presentation).length,
      (([Q] : Presentation).get k).map (fun d ↦ (e d.1, if flip d.1 then !d.2 else d.2)) =
        ([normalWord g b'] : Presentation).get k := by
    intro k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    exact he
  obtain ⟨H, hH, hEdge⟩ := labelRenaming_realized (P := [Q]) (Q := [normalWord g b']) e flip (Equiv.refl _) hword
  let tail : RealizedSequence [Q] [normalWord g b'] :=
    .cons (.rename (Q := [normalWord g b']) e flip (Equiv.refl _) (fun k ↦ (hword k) ▸ List.IsRotated.refl _)) H hH (.nil _)
  let sn := s.trans tail
  obtain ⟨σ, hσ⟩ := sequence_to_normal_boundary K o H₀ hH₀ B hboundary sn
  have hbb : b = b' := by simpa using Fintype.card_congr σ
  subst b'
  let c : PolygonReductionCore K o B :=
    { g := g, Q := [normalWord g b], e := Equiv.refl ℕ, flip := fun _ ↦ false,
      f := Equiv.refl _, wordEq := by intro k; simp }
  exact ⟨c, ⟨sn⟩, trivial⟩

/--
Source: Gallier–Xu Proposition 3.2 p.31, Note F.4 p.167, and Lemma 6.1
pp.92–95. Every move preserves the union of singly occurring edge images.
Original parameters identify that union with the given cycle carriers. These
cycles and the canonical loops are finite disjoint nonempty compact connected
pieces; connectedness makes their containing-piece maps inverse. Append the
signed relabeling, obtain this bijection, and pull its edge-image equations
back through the relabeling homeomorphism.
-/
theorem polygon_reduction_boundary
    {N b : ℕ} (K : AbstractSimplicialComplex (Fin N)) (_hb : 1 ≤ b)
    (_hpure : PureTwo K) (_hconnected : IsConnected (carrier K))
    (_hincidence : ∀ e ∈ simplices K 1, incidence K e = 1 ∨ incidence K e = 2)
    (_hlinks : SurfaceLinks K) (B : Fin b → List (Fin N)) (hboundary : BoundaryCycles K B)
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (_horiented : Oriented (trianglePresentation K o))
    (H₀ : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o))
    (hH₀ : OriginalParameters K o H₀)
    (c : PolygonReductionCore K o B) (s : PolygonReductionWithSequence c) :
    ∃ _q : PolygonReductionWithBoundary (H₀ := H₀) c s, True := by
  obtain ⟨H, hH, hEdge⟩ := labelRenaming_realized c.e c.flip c.f c.wordEq
  let tail : RealizedSequence c.Q [normalWord c.g b] :=
    .cons (.rename c.e c.flip c.f (fun k ↦ (c.wordEq k) ▸ List.IsRotated.refl _)) H hH (.nil _)
  obtain ⟨σ, hσ⟩ := sequence_to_normal_boundary K o H₀ hH₀ B hboundary
    (s.sequence.trans tail)
  refine ⟨⟨σ, ?_⟩, trivial⟩
  intro j
  apply H.injective.image_injective
  rw [hEdge, c.e.apply_symm_apply]
  have hh := hσ j
  have hmap : (H₀.trans (s.sequence.trans tail).homeomorph) =
      (H₀.trans s.sequence.homeomorph).trans H := by
    ext x
    simp only [Homeomorph.trans_apply, RealizedSequence.trans_homeomorph_apply]
    rfl
  rw [hmap] at hh
  change (H ∘ (H₀.trans s.sequence.homeomorph)) '' _ = _ at hh
  exact (Set.image_image _ _ _).trans hh

/--
Source: Gallier–Xu Theorem 6.1 p.96, formal invariants pp.87–89 and Lemma 6.1
Step 6 p.95. Count the finite set of incoming-dart classes generated by the
literal corner relation. P1 adds precisely its new midpoint class and one edge;
P2 keeps the classes and adds one edge and one face. Rotations, reindexings and
signed renamings induce class bijections. Thus every realized sequence preserves
V-E+F. At the original triangles, each corner preserves its terminal vertex,
and the given interval or circle link connects all incoming edges at a vertex;
purity identifies the edge labels with the original two-vertex simplices. At
normalWord g b, every handle dart and each negative spoke belongs to the base
class; the positive spoke and both signs of its boundary loop form one further
class per loop. A finite classifier proves these are exactly b+1 classes.
Together with 2g+2b labels and one face, the count is 2-2g-b.
-/
theorem polygon_reduction_euler
    {N b : ℕ} (K : AbstractSimplicialComplex (Fin N)) (hb : 1 ≤ b)
    (hpure : PureTwo K) (_hconnected : IsConnected (carrier K))
    (_hincidence : ∀ e ∈ simplices K 1, incidence K e = 1 ∨ incidence K e = 2)
    (hlinks : SurfaceLinks K) (B : Fin b → List (Fin N)) (hboundary : BoundaryCycles K B)
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (_horiented : Oriented (trianglePresentation K o))
    (H₀ : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o))
    (_hH₀ : OriginalParameters K o H₀)
    (c : PolygonReductionCore K o B) (s : PolygonReductionWithSequence c)
    (_q : PolygonReductionWithBoundary (H₀ := H₀) c s) :
    ((simplices K 0).card : ℤ) - ((simplices K 1).card : ℤ) +
      ((simplices K 2).card : ℤ) = (2 : ℤ) - 2 * (c.g : ℤ) - (b : ℤ) := by
  have hb0 : 0 < b := by omega
  obtain ⟨l, tail, hl⟩ := List.exists_cons_of_ne_nil (show B ⟨0, hb0⟩ ≠ [] from by
    intro he
    have hh := (hboundary.1 ⟨0, hb0⟩).2
    simp [he] at hh)
  have hstart := trianglePresentation_euler K hpure hlinks o l
  have hend := presentationEuler_rename c.e c.flip c.f
    (fun k ↦ (c.wordEq k) ▸ List.IsRotated.refl _)
  have hs := s.sequence.euler
  rw [normalWord_presentationEuler c.g b hb0] at hend
  exact hstart.symm.trans (hs.trans hend)

theorem orientable_triangle_presentation_reduction_witness
    {N b : ℕ} (K : AbstractSimplicialComplex (Fin N)) (hb : 1 ≤ b)
    (hpure : PureTwo K) (hconnected : IsConnected (carrier K))
    (hincidence : ∀ e ∈ simplices K 1, incidence K e = 1 ∨ incidence K e = 2)
    (hlinks : SurfaceLinks K) (B : Fin b → List (Fin N)) (hboundary : BoundaryCycles K B)
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (horiented : Oriented (trianglePresentation K o))
    (H₀ : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o))
    (hH₀ : OriginalParameters K o H₀) :
    ∃ _w : PolygonReductionWitness K o H₀ B, True := by
  obtain ⟨c, s, _⟩ := polygon_reduction_sequence K hb hpure hconnected hincidence hlinks B hboundary
    o horiented H₀ hH₀
  obtain ⟨q, _⟩ := polygon_reduction_boundary K hb hpure hconnected hincidence hlinks B hboundary
    o horiented H₀ hH₀ c s
  have he := polygon_reduction_euler K hb hpure hconnected hincidence hlinks B hboundary
    o horiented H₀ hH₀ c s q
  let w : PolygonReductionWitness K o H₀ B :=
    { g := c.g, Q := c.Q, e := c.e, flip := c.flip, f := c.f, wordEq := c.wordEq
      sequence := s.sequence, sigma := q.sigma, boundaryEq := q.boundaryEq, eulerEq := he }
  exact ⟨w, trivial⟩


end HolomorphicAnosov.Topology.GallierXu
