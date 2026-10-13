import HolomorphicAnosov.Geometry.LyubichMarkedTriangleTopologyProviders
import Mathlib.Topology.Order.IntermediateValue
import HolomorphicAnosov.Geometry.IdealTriangleReflectionTilingCoreG6
import HolomorphicAnosov.Geometry.IdealTriangleSideBoundaryG6
import HolomorphicAnosov.Geometry.IdealTriangleItineraryReductionG6

/-! This file proves that reflections in the sides of an ideal triangle tile the open disk by reflected triangles. (Epstein–Petronio, Thm. 5.5) -/

noncomputable section

namespace HolomorphicAnosov.IdealDiskTriangle
open scoped ComplexConjugate
set_option maxHeartbeats 1000000

/-- A reflected reached triangle remains reached, and reflection exchanges the literal carriers in both directions. -/
lemma reached_reflection_carriers (V : VertexTriple) (A : ReachedTriangle V)
    {p q : ℂ} (hp : p ∈ A.val.val) (hq : q ∈ A.val.val) (hpq : p ≠ q) :
    ∃ B : ReachedTriangle V,
      B.val.val = reflectedVertices A.val.val p q ∧ A ≠ B ∧
      hasSide B.val.val (openSide p q) ∧
      (∀ z ∈ openSide p q, idealDiskSideReflection p q z = z) ∧
      idealDiskSideReflection p q '' disk = disk ∧
      (∀ z ∈ disk, idealDiskSideReflection p q (idealDiskSideReflection p q z) = z) ∧
      idealDiskSideReflection p q '' triangle A.val.val = triangle B.val.val ∧
      idealDiskSideReflection p q '' triangle B.val.val = triangle A.val.val := by
  classical
  have hstep : reflectionStep A.val.val (reflectedVertices A.val.val p q) :=
    ⟨p,hp,q,hq,hpq,rfl⟩
  let B : ReachedTriangle V := ⟨⟨reflectedVertices A.val.val p q,
    reflectionStep_preserves_vertexTriple _ A.val.property hstep⟩, A.property.tail hstep⟩
  have hpu := A.val.property.2 p hp
  have hqu := A.val.property.2 q hq
  have hfix := idealDiskSideReflection_endpoints hpu hqu hpq
  have himg : idealDiskSideReflection p q '' triangle A.val.val = triangle B.val.val :=
    idealDiskSideReflection_triangle_image_g6 A.val hpu hqu hpq hp hq
  refine ⟨B,rfl,?_,?_,?_,idealDiskSideReflection_disk_image_g6 hpu hqu hpq,
    idealDiskSideReflection_involutive_disk_g6 hpu hqu hpq,himg,?_⟩
  · intro heq
    exact reflectedVertices_ne_self A.val hp hq hpq
      (congrArg (fun X : ReachedTriangle V ↦ X.val.val) heq).symm
  · refine ⟨p,?_,q,?_,hpq,rfl⟩
    · exact Finset.mem_image.mpr ⟨p,hp,hfix.1⟩
    · exact Finset.mem_image.mpr ⟨q,hq,hfix.2⟩
  · exact fun z hz ↦ idealDiskSideReflection_fixed_openSide hpu hqu hpq hz
  · rw [← himg, Set.image_image]
    apply Set.Subset.antisymm
    · rintro z ⟨w,hw,rfl⟩
      simpa only [Function.comp_apply, idealDiskSideReflection_involutive_disk_g6 hpu hqu hpq w hw.1] using hw
    · intro z hz
      exact ⟨z,hz,idealDiskSideReflection_involutive_disk_g6 hpu hqu hpq z hz.1⟩

lemma reached_adjacent_unique_side (V : VertexTriple) (A B : ReachedTriangle V)
    (hAB : (dualGraph V).Adj A B) :
    ∃! S : ReachedSide V, hasSide A.val.val S.val ∧ hasSide B.val.val S.val := by
  obtain ⟨hne,S,hAS,hBS⟩ := hAB
  refine ⟨⟨S,A,hAS⟩,⟨hAS,hBS⟩,?_⟩
  intro T hT
  apply Subtype.ext
  exact sharedSide_unique (fun h ↦ hne (congrArg Subtype.val h)) hT.1 hT.2 hAS hBS

private lemma norm_klein_lt_one {z : ℂ} (hz : ‖z‖ < 1) : ‖idealDiskKlein z‖ < 1 := by
  have hs : 0 < 1+‖z‖ ^ 2 := by positivity
  rw [idealDiskKlein, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs, div_lt_one hs]
  nlinarith [sq_pos_of_pos (sub_pos.mpr hz)]

private lemma negative_side_preconnected (p q r : ℂ) :
    IsPreconnected {z : ℂ | z ∈ disk ∧ sideEquation p q z * sideEquation p q r < 0} := by
  let C : Set ℂ := {w | ‖w‖ < 1 ∧ linearSideEquation p q w * sideEquation p q r < 0}
  have hEq : idealDiskKleinInv '' C =
      {z : ℂ | z ∈ disk ∧ sideEquation p q z * sideEquation p q r < 0} := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      obtain ⟨hz,t,ht,he,hrad⟩ := kleinInv_radial_identity hw.1
      obtain ⟨a,ha,hside⟩ := sideEquation_inverse_radial (p := p) (q := q) hw.1
      simp only [Complex.ofReal_add, Complex.ofReal_one] at hside hz
      change sideEquation p q (idealDiskKleinInv w) = a * linearSideEquation p q w at hside
      refine ⟨hz,?_⟩
      rw [hside,mul_assoc]
      exact mul_neg_of_pos_of_neg ha hw.2
    · rintro ⟨hzD,hz⟩
      have hw := norm_klein_lt_one hzD
      refine ⟨idealDiskKlein z, ⟨hw,?_⟩, idealDiskKleinInv_left hzD⟩
      obtain ⟨a,ha,hside⟩ := sideEquation_inverse_radial (p := p) (q := q) hw
      simp only [Complex.ofReal_add, Complex.ofReal_one] at hside
      change sideEquation p q (idealDiskKleinInv (idealDiskKlein z)) =
        a * linearSideEquation p q (idealDiskKlein z) at hside
      rw [idealDiskKleinInv_left hzD] at hside
      rw [hside,mul_assoc] at hz
      have : linearSideEquation p q (idealDiskKlein z) * sideEquation p q r < 0 := by
        nlinarith
      exact this
  rw [← hEq]
  apply (convex_linear_side_cap p q r).isPreconnected.image
  change ContinuousOn (fun w : ℂ ↦ w / (1 + (Real.sqrt (1-‖w‖ ^ 2) : ℂ))) C
  simpa only [Complex.ofReal_add, Complex.ofReal_one] using
    continuous_side_radial_inv.continuousOn (s := C)

private lemma reflection_side_product_neg_iff {p q r z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) (hz : z ∈ disk) :
    sideEquation p q (idealDiskSideReflection p q z) * sideEquation p q r < 0 ↔
      0 < sideEquation p q z * sideEquation p q r := by
  rw [← not_le, idealDiskSideReflection_halfspace_sign_g6 hp hq hpq hz, not_le]

private lemma exists_negative_side_in_nhds {p q r z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q)
    (hr : sideEquation p q r ≠ 0) (hz : z ∈ openSide p q)
    {U : Set ℂ} (hU : U ∈ nhds z) :
    ∃ w ∈ U, w ∈ disk ∧ sideEquation p q w * sideEquation p q r < 0 := by
  have hcont : ContinuousAt (idealDiskSideReflection p q) z := by
    unfold idealDiskSideReflection
    exact (continuousAt_const.sub (continuousAt_const.mul Complex.continuous_conj.continuousAt)).div
      (continuousAt_const.sub (continuousAt_const.mul Complex.continuous_conj.continuousAt))
      (idealDiskSideReflection_denominator_ne_zero_g6 hp hq hz.1)
  have hUR : idealDiskSideReflection p q ⁻¹' U ∈ nhds z := by
    apply hcont.preimage_mem_nhds
    simpa only [idealDiskSideReflection_fixed_openSide hp hq hpq hz] using hU
  have hD : disk ∈ nhds z := (isOpen_lt continuous_norm continuous_const).mem_nhds hz.1
  have hN : U ∩ (idealDiskSideReflection p q ⁻¹' U) ∩ disk ∈ nhds z :=
    Filter.inter_mem (Filter.inter_mem hU hUR) hD
  have hnonsub : ¬ U ∩ (idealDiskSideReflection p q ⁻¹' U) ∩ disk ⊆
      {w | sideEquation p q w = 0} := by
    intro hsub
    have hzint := mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hN hsub)
    rw [interior_sideEquation_zero_eq_empty hp] at hzint
    exact hzint
  obtain ⟨w,hw,hwn⟩ := Set.not_subset.mp hnonsub
  have hprod : sideEquation p q w * sideEquation p q r ≠ 0 := mul_ne_zero hwn hr
  rcases lt_or_gt_of_ne hprod with hneg | hpos
  · exact ⟨w,hw.1.1,hw.2,hneg⟩
  · exact ⟨idealDiskSideReflection p q w,hw.1.2,
      idealDiskSideReflection_mem_disk_g6 hp hq hpq hw.2,
      (reflection_side_product_neg_iff hp hq hpq hw.2).mpr hpos⟩

/-- An exterior region of one triangle side lies strictly inside either of the other side half-spaces. -/
private lemma negative_side_other_positive (A : VertexTriple) {p q r w : ℂ}
    (hp : p ∈ A.val) (hq : q ∈ A.val) (hr : r ∈ A.val)
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hw : w ∈ disk) (hneg : sideEquation p q w * sideEquation p q r < 0) :
    0 < sideEquation q r w * sideEquation q r p := by
  have hpu := A.property.2 p hp
  have hqu := A.property.2 q hq
  have hru := A.property.2 r hr
  have hrnon : sideEquation p q r ≠ 0 := by
    intro he
    exact (eq_endpoint_of_sideEquation_eq_zero_unit hpu hqu hru he).elim hrp hqr.symm
  have hpnon : sideEquation q r p ≠ 0 := by
    intro he
    exact (eq_endpoint_of_sideEquation_eq_zero_unit hqu hru hpu he).elim hpq hrp.symm
  have hside : (openSide p q).Nonempty := by
    by_contra hn
    have he : openSide p q = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hcl := left_mem_closure_openSide hpu hqu hpq
    rw [he,closure_empty] at hcl
    exact hcl
  obtain ⟨z,hz⟩ := hside
  have hzA := openSide_mem_triangle_of_vertexTriple A hp hq hpq hz
  have hzq : sideEquation q r z ≠ 0 := by
    intro he
    have hd := openSide_disjoint_of_common_endpoint hqu hpu hru hpq.symm hqr hrp.symm
    exact Set.disjoint_left.mp hd (openSide_comm p q ▸ hz) ⟨hz.1,he⟩
  have hzpos : 0 < sideEquation q r z * sideEquation q r p :=
    lt_of_le_of_ne (hzA.2 q hq r hr p hp hqr hrp hpq) (Ne.symm (mul_ne_zero hzq hpnon))
  have hU := (isOpen_lt continuous_const ((continuous_sideEquation q r).mul_const
    (sideEquation q r p))).mem_nhds hzpos
  obtain ⟨v,hvpos,hvD,hvneg⟩ := exists_negative_side_in_nhds hpu hqu hpq hrnon hz hU
  let C : Set ℂ := {x | x ∈ disk ∧ sideEquation p q x * sideEquation p q r < 0}
  have hzero : ∀ x ∈ C, sideEquation q r x * sideEquation q r p ≠ 0 := by
    intro x hx he
    have he' : sideEquation q r x = 0 := (mul_eq_zero.mp he).resolve_right hpnon
    have hxA := openSide_mem_triangle_of_vertexTriple A hq hr hqr ⟨hx.1,he'⟩
    exact (not_lt_of_ge (hxA.2 p hp q hq r hr hpq hqr hrp)) hx.2
  by_contra! hnot
  have hmem : (0:ℝ) ∈ Set.Icc (sideEquation q r w * sideEquation q r p)
      (sideEquation q r v * sideEquation q r p) := ⟨hnot,hvpos.le⟩
  obtain ⟨x,hx,hxe⟩ := (negative_side_preconnected p q r).intermediate_value
    (show w ∈ C from ⟨hw,hneg⟩) (show v ∈ C from ⟨hvD,hvneg⟩)
    (((continuous_sideEquation q r).mul_const _).continuousOn) hmem
  exact hzero x hx hxe

set_option maxRecDepth 4096 in
private lemma reflection_conjugacy {p q a b z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hpq : p ≠ q) (hab : a ≠ b) (hz : ‖z‖ ≤ 1) :
    idealDiskSideReflection (idealDiskSideReflection p q a)
      (idealDiskSideReflection p q b) (idealDiskSideReflection p q z) =
      idealDiskSideReflection p q (idealDiskSideReflection a b z) := by
  have haR := reflection_unit hp hq hpq ha
  have hbR := reflection_unit hp hq hpq hb
  have habR : idealDiskSideReflection p q a ≠ idealDiskSideReflection p q b :=
    fun he ↦ hab (reflection_inj_closed hp hq hpq ha.le hb.le he)
  have hzR : ‖idealDiskSideReflection p q z‖ ≤ 1 := by
    rcases lt_or_eq_of_le hz with hz | hz
    · exact (idealDiskSideReflection_mem_disk_g6 hp hq hpq hz).le
    · exact (reflection_unit hp hq hpq hz).le
  have hzAB : ‖idealDiskSideReflection a b z‖ ≤ 1 := by
    rcases lt_or_eq_of_le hz with hz | hz
    · exact (idealDiskSideReflection_mem_disk_g6 ha hb hab hz).le
    · exact (reflection_unit ha hb hab hz).le
  have hdpa := reflection_denominator_closed hp hq hpq ha.le
  have hdpb := reflection_denominator_closed hp hq hpq hb.le
  have hdpz := reflection_denominator_closed hp hq hpq hz
  have hdaz := reflection_denominator_closed ha hb hab hz
  have hdL := reflection_denominator_closed haR hbR habR hzR
  have hdR := reflection_denominator_closed hp hq hpq hzAB
  have hpc : conj p = 1/p := by
    apply (eq_div_iff (norm_ne_zero_iff.mp (by rw [hp]; norm_num))).mpr
    rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq,hp]
    norm_num
  have hqc : conj q = 1/q := by
    apply (eq_div_iff (norm_ne_zero_iff.mp (by rw [hq]; norm_num))).mpr
    rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq,hq]
    norm_num
  have hac : conj a = 1/a := by
    apply (eq_div_iff (norm_ne_zero_iff.mp (by rw [ha]; norm_num))).mpr
    rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq,ha]
    norm_num
  have hbc : conj b = 1/b := by
    apply (eq_div_iff (norm_ne_zero_iff.mp (by rw [hb]; norm_num))).mpr
    rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq,hb]
    norm_num
  have hpn : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hp]; norm_num)
  have hqn : q ≠ 0 := norm_ne_zero_iff.mp (by rw [hq]; norm_num)
  have han : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  have hbn : b ≠ 0 := norm_ne_zero_iff.mp (by rw [hb]; norm_num)
  have hdpc := (map_ne_zero (starRingEnd ℂ)).mpr hdpz
  have hdac := (map_ne_zero (starRingEnd ℂ)).mpr hdaz
  simp only [map_sub,map_add,map_mul,map_ofNat,Complex.conj_conj,hpc,hqc,hac,hbc]
    at hdpa hdpb hdpc hdac
  unfold idealDiskSideReflection at hdL hdR ⊢
  apply (div_eq_div_iff hdL hdR).mpr
  simp only [map_div₀,map_sub,map_add,map_mul,map_ofNat,Complex.conj_conj,hpc,hqc,hac,hbc]
  field_simp [hpn,hqn,han,hbn] at hdpa hdpb hdpc hdac
  have hdpa' := (div_ne_zero_iff.mp hdpa).1
  have hdpb' := (div_ne_zero_iff.mp hdpb).1
  have hdpc' := (div_ne_zero_iff.mp hdpc).1
  have hdac' := (div_ne_zero_iff.mp hdac).1
  have hdpc'' : p*q*2-(q+p)*z ≠ 0 := by
    intro h
    apply hdpc'
    linear_combination h
  field_simp (disch := solve | assumption | norm_num | (intro h; solve
    | (apply hdpa'; linear_combination h)
    | (apply hdpb'; linear_combination h)
    | (apply hdpc'; linear_combination h)
    | (apply hdac'; linear_combination h)))
  ring

private lemma reflected_vertices_triple (A : VertexTriple) {p q : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) :
    (reflectedVertices A.val p q).card = 3 ∧
      ∀ z ∈ reflectedVertices A.val p q, ‖z‖ = 1 := by
  classical
  constructor
  · rw [reflectedVertices, Finset.card_image_of_injOn, A.property.1]
    intro x hx y hy hxy
    exact reflection_inj_closed hp hq hpq (A.property.2 x hx).le
      (A.property.2 y hy).le hxy
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact reflection_unit hp hq hpq (A.property.2 x hx)

/-- Reflecting the entire reached family in an original side preserves it. -/
private lemma base_reflection_preserves_reached (V : VertexTriple) {p q : ℂ}
    (hp : p ∈ V.val) (hq : q ∈ V.val) (hpq : p ≠ q)
    (W : Finset ℂ) (hW : reachable V.val W) :
    reachable V.val (reflectedVertices W p q) ∧
      triangle (reflectedVertices W p q) = idealDiskSideReflection p q '' triangle W := by
  classical
  have hpu := V.property.2 p hp
  have hqu := V.property.2 q hq
  induction hW with
  | refl =>
    exact ⟨Relation.ReflTransGen.single ⟨p,hp,q,hq,hpq,rfl⟩,
      (idealDiskSideReflection_triangle_image_g6 V hpu hqu hpq hp hq).symm⟩
  | @tail W U hW hWU ih =>
    obtain ⟨a,ha,b,hb,hab,rfl⟩ := hWU
    let A : VertexTriple := ⟨W,reachable_preserves_vertexTriple V W hW⟩
    let B : VertexTriple := ⟨reflectedVertices W p q,reflected_vertices_triple A hpu hqu hpq⟩
    have hau := A.property.2 a ha
    have hbu := A.property.2 b hb
    have haB : idealDiskSideReflection p q a ∈ B.val := Finset.mem_image.mpr ⟨a,ha,rfl⟩
    have hbB : idealDiskSideReflection p q b ∈ B.val := Finset.mem_image.mpr ⟨b,hb,rfl⟩
    have habB : idealDiskSideReflection p q a ≠ idealDiskSideReflection p q b :=
      fun he ↦ hab (reflection_inj_closed hpu hqu hpq hau.le hbu.le he)
    have hvertices : reflectedVertices (reflectedVertices W a b) p q =
        reflectedVertices B.val (idealDiskSideReflection p q a) (idealDiskSideReflection p q b) := by
      simp only [reflectedVertices, B, Finset.image_image]
      apply Finset.image_congr
      intro z hz
      exact (reflection_conjugacy hpu hqu hau hbu hpq hab (A.property.2 z hz).le).symm
    rw [hvertices]
    refine ⟨ih.1.tail ⟨_,haB,_,hbB,habB,rfl⟩,?_⟩
    rw [← idealDiskSideReflection_triangle_image_g6 B
      (reflection_unit hpu hqu hpq hau) (reflection_unit hpu hqu hpq hbu) habB haB hbB]
    change idealDiskSideReflection (idealDiskSideReflection p q a) (idealDiskSideReflection p q b) ''
      triangle (reflectedVertices W p q) = _
    rw [ih.2, ← idealDiskSideReflection_triangle_image_g6 A hau hbu hab ha hb,
      Set.image_image,Set.image_image]
    apply Set.image_congr
    intro z hz
    exact reflection_conjugacy hpu hqu hau hbu hpq hab hz.1.le

/-- Every disk point lies in a reached triangle. -/
private lemma reached_carriers_cover (V : VertexTriple) (z : disk) :
    ∃ A : ReachedTriangle V, z.val ∈ triangle A.val.val := by
  classical
  by_contra hz
  let S : Set ℂ := {w | w ∈ disk ∧ ¬ ∃ A : ReachedTriangle V, w ∈ triangle A.val.val}
  have hS : S.Nonempty := ⟨z.val,z.property,hz⟩
  have hSd : S ⊆ disk := fun _ hw ↦ hw.1
  have hinv : ∀ p ∈ V.val, ∀ q ∈ V.val, p ≠ q →
      idealDiskSideReflection p q '' S ⊆ S := by
    intro p hp q hq hpq w hw
    obtain ⟨v,hv,rfl⟩ := hw
    have hpu := V.property.2 p hp
    have hqu := V.property.2 q hq
    refine ⟨idealDiskSideReflection_mem_disk_g6 hpu hqu hpq hv.1,?_⟩
    rintro ⟨A,hA⟩
    obtain ⟨hr,he⟩ := base_reflection_preserves_reached V hp hq hpq A.val.val A.property
    let B : ReachedTriangle V := ⟨⟨_,reflected_vertices_triple A.val hpu hqu hpq⟩,hr⟩
    apply hv.2
    refine ⟨B,?_⟩
    change v ∈ triangle (reflectedVertices A.val.val p q)
    rw [he]
    exact ⟨idealDiskSideReflection p q v,hA,
      idealDiskSideReflection_involutive_disk_g6 hpu hqu hpq v hv.1⟩
  obtain ⟨w,hwS,hwV⟩ := invariant_set_meets_triangle V hS hSd
    (fun p hp q hq hpq w hw ↦ hinv p hp q hq hpq ⟨w,hw,rfl⟩)
  exact hwS.2 ⟨initialTriangle V,hwV⟩

private lemma triangle_third_vertex (A : VertexTriple) {p q : ℂ}
    (hp : p ∈ A.val) (hq : q ∈ A.val) (hpq : p ≠ q) :
    ∃ r ∈ A.val, q ≠ r ∧ r ≠ p ∧ A.val = {p,q,r} := by
  classical
  obtain ⟨r,hr,hrpq⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {p,q}) (t := A.val) (by rw [Finset.card_pair hpq,A.property.1]; norm_num)
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hrpq
  refine ⟨r,hr,Ne.symm hrpq.2,hrpq.1,?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hp ⟨hq,hr⟩
  · rw [A.property.1]
    simp [hpq,Ne.symm hrpq.1,Ne.symm hrpq.2]

private lemma interior_side_positive (A : VertexTriple) {p q r z : ℂ}
    (hp : p ∈ A.val) (hq : q ∈ A.val) (hr : r ∈ A.val)
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hz : z ∈ openTriangle A.val) :
    0 < sideEquation p q z * sideEquation p q r := by
  have hzA : z ∈ triangle A.val := interior_subset hz
  have hzr : sideEquation p q z ≠ 0 := fun he ↦
    openSide_not_mem_openTriangle A hp hq hpq ⟨hzA.1,he⟩ hz
  have hrr : sideEquation p q r ≠ 0 := by
    intro he
    exact (eq_endpoint_of_sideEquation_eq_zero_unit (A.property.2 p hp)
      (A.property.2 q hq) (A.property.2 r hr) he).elim hrp hqr.symm
  exact lt_of_le_of_ne (hzA.2 p hp q hq r hr hpq hqr hrp)
    (Ne.symm (mul_ne_zero hzr hrr))

private lemma reflected_reference_opposite (A B : VertexTriple) {p q r t : ℂ}
    (hp : p ∈ A.val) (hq : q ∈ A.val) (hr : r ∈ A.val)
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hB : B.val = reflectedVertices A.val p q)
    (ht : t ∈ B.val) (hqt : q ≠ t) (htp : t ≠ p) :
    sideEquation p q r * sideEquation p q t < 0 := by
  have hpu := A.property.2 p hp
  have hqu := A.property.2 q hq
  have hfix := idealDiskSideReflection_endpoints hpu hqu hpq
  have hpB : p ∈ B.val := by rw [hB]; exact Finset.mem_image.mpr ⟨p,hp,hfix.1⟩
  have hqB : q ∈ B.val := by rw [hB]; exact Finset.mem_image.mpr ⟨q,hq,hfix.2⟩
  obtain ⟨z,hz⟩ := normalized_triangle_carrier_nonempty_g6 A
  have hzA : z ∈ triangle A.val := interior_subset hz
  have hzpos := interior_side_positive A hp hq hr hpq hqr hrp hz
  have hzneg := (reflection_side_product_neg_iff hpu hqu hpq hzA.1).mpr hzpos
  have hzB : idealDiskSideReflection p q z ∈ triangle B.val := by
    rw [hB]
    exact (idealDiskSideReflection_triangle_transport_vertex_g6 A hpu hqu hpq hp hq z).1 hzA
  have htnon : sideEquation p q t ≠ 0 := by
    intro he
    exact (eq_endpoint_of_sideEquation_eq_zero_unit hpu hqu (B.property.2 t ht) he).elim htp hqt.symm
  have hznon : sideEquation p q (idealDiskSideReflection p q z) ≠ 0 := by
    intro he
    rw [he,zero_mul] at hzneg
    exact (lt_irrefl 0 hzneg)
  have hzposB : 0 < sideEquation p q (idealDiskSideReflection p q z) * sideEquation p q t :=
    lt_of_le_of_ne (hzB.2 p hpB q hqB t ht hpq hqt htp)
      (Ne.symm (mul_ne_zero hznon htnon))
  rcases lt_or_gt_of_ne hznon with hs | hs
  · have hrpos : 0 < sideEquation p q r := by nlinarith
    have htneg : sideEquation p q t < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg hrpos htneg
  · have hrneg : sideEquation p q r < 0 := by nlinarith
    have htpos : 0 < sideEquation p q t := by nlinarith
    exact mul_neg_of_neg_of_pos hrneg htpos

private lemma other_side_positive (A : VertexTriple) {p q r a b c z : ℂ}
    (hp : p ∈ A.val) (hq : q ∈ A.val) (hr : r ∈ A.val)
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (ha : a ∈ A.val) (hb : b ∈ A.val) (hc : c ∈ A.val)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hside : openSide p q ≠ openSide a b)
    (hz : z ∈ disk) (hneg : sideEquation p q z * sideEquation p q r < 0) :
    0 < sideEquation a b z * sideEquation a b c := by
  classical
  have hA : A.val = {p,q,r} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hp ⟨hq,hr⟩
    · rw [A.property.1]; simp [hpq,Ne.symm hrp,hqr]
  have hpos₁ := negative_side_other_positive A hp hq hr hpq hqr hrp hz hneg
  have hpos₂ := negative_side_other_positive A hq hp hr hpq.symm hrp.symm hqr.symm hz
    (by rw [← sideEquation_swap_product]; exact hneg)
  simp only [hA,Finset.mem_insert,Finset.mem_singleton] at ha hb hc
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;>
    first | exact (hab rfl).elim | exact (hbc rfl).elim | exact (hca rfl).elim |
      exact (hside rfl).elim | exact (hside (openSide_comm _ _)).elim |
      exact hpos₁ | exact hpos₂ |
      (rw [← sideEquation_swap_product]; assumption)

private lemma reflectionStep_symm {A B : VertexTriple}
    (h : reflectionStep A.val B.val) : reflectionStep B.val A.val := by
  classical
  obtain ⟨p,hp,q,hq,hpq,hB⟩ := h
  have hpu := A.property.2 p hp
  have hqu := A.property.2 q hq
  have hfix := idealDiskSideReflection_endpoints hpu hqu hpq
  have hpB : p ∈ B.val := by rw [hB]; exact Finset.mem_image.mpr ⟨p,hp,hfix.1⟩
  have hqB : q ∈ B.val := by rw [hB]; exact Finset.mem_image.mpr ⟨q,hq,hfix.2⟩
  let C : VertexTriple := ⟨reflectedVertices B.val p q,
    reflectionStep_preserves_vertexTriple _ B.property ⟨p,hpB,q,hqB,hpq,rfl⟩⟩
  have hcar : triangle B.val = idealDiskSideReflection p q '' triangle A.val := by
    rw [hB]
    exact (idealDiskSideReflection_triangle_image_g6 A hpu hqu hpq hp hq).symm
  have hback : triangle C.val = triangle A.val := by
    rw [show triangle C.val = idealDiskSideReflection p q '' triangle B.val from
      (idealDiskSideReflection_triangle_image_g6 B hpu hqu hpq hpB hqB).symm,
      hcar,Set.image_image]
    apply Set.Subset.antisymm
    · rintro z ⟨w,hw,rfl⟩
      simpa only [Function.comp_apply,
        idealDiskSideReflection_involutive_disk_g6 hpu hqu hpq w hw.1] using hw
    · intro z hz
      exact ⟨z,hz,idealDiskSideReflection_involutive_disk_g6 hpu hqu hpq z hz.1⟩
  have he := congrArg Subtype.val (triangle_vertexTriple_injective hback)
  exact ⟨p,hpB,q,hqB,hpq,he.symm⟩

lemma reflection_eq_of_side_eq {p q a b : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hpq : p ≠ q) (hab : a ≠ b) (he : openSide p q = openSide a b) :
    idealDiskSideReflection p q = idealDiskSideReflection a b := by
  have hend {x : ℂ} (hx : x = p ∨ x = q) : x = a ∨ x = b := by
    have hxunit : ‖x‖ = 1 := hx.elim (fun h ↦ h ▸ hp) (fun h ↦ h ▸ hq)
    have hxcl : x ∈ closure (openSide p q) := by
      rcases hx with rfl | rfl
      · exact left_mem_closure_openSide hp hq hpq
      · rw [openSide_comm]
        exact left_mem_closure_openSide hq hp hpq.symm
    rw [he] at hxcl
    have hxzero : sideEquation a b x = 0 :=
      closure_minimal (fun _ h ↦ h.2)
        (isClosed_eq (continuous_sideEquation a b) continuous_const) hxcl
    exact eq_endpoint_of_sideEquation_eq_zero_unit ha hb hxunit hxzero
  rcases hend (x := p) (Or.inl rfl) with rfl | rfl <;>
    rcases hend (x := q) (Or.inr rfl) with h | h
  · exact (hpq h.symm).elim
  · subst q; rfl
  · subst q
    funext z
    unfold idealDiskSideReflection
    congr 1 <;> ring
  · exact (hpq h.symm).elim

private def across (A B : VertexTriple) : Set ℂ :=
  {z | z ∈ disk ∧ ∃ p ∈ A.val, ∃ q ∈ A.val, ∃ r ∈ A.val,
    p ≠ q ∧ q ≠ r ∧ r ≠ p ∧ B.val = reflectedVertices A.val p q ∧
      sideEquation p q z * sideEquation p q r < 0}

private lemma across_disjoint_source (A B : VertexTriple) :
    Disjoint (triangle A.val) (across A B) := by
  apply Set.disjoint_left.mpr
  rintro z hz ⟨hzD,p,hp,q,hq,r,hr,hpq,hqr,hrp,hB,hneg⟩
  exact (not_lt_of_ge (hz.2 p hp q hq r hr hpq hqr hrp)) hneg

private lemma mul_negative_of_opposite {x a b : ℝ} (hab : a*b < 0) (hxb : 0 < x*b) :
    x*a < 0 := by
  rcases mul_neg_iff.mp hab with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have hx : x < 0 := by nlinarith
    exact mul_neg_of_neg_of_pos hx ha
  · have hx : 0 < x := by nlinarith
    exact mul_neg_of_pos_of_neg hx ha

private lemma interior_subset_across {A B : VertexTriple}
    (hAB : reflectionStep A.val B.val) : openTriangle B.val ⊆ across A B := by
  obtain ⟨p,hp,q,hq,hpq,hB⟩ := hAB
  obtain ⟨r,hr,hqr,hrp,_⟩ := triangle_third_vertex A hp hq hpq
  have hfix := idealDiskSideReflection_endpoints (A.property.2 p hp) (A.property.2 q hq) hpq
  have hpB : p ∈ B.val := by rw [hB]; exact Finset.mem_image.mpr ⟨p,hp,hfix.1⟩
  have hqB : q ∈ B.val := by rw [hB]; exact Finset.mem_image.mpr ⟨q,hq,hfix.2⟩
  obtain ⟨t,ht,hqt,htp,_⟩ := triangle_third_vertex B hpB hqB hpq
  have hopp := reflected_reference_opposite A B hp hq hr hpq hqr hrp hB ht hqt htp
  intro z hz
  exact ⟨(interior_subset hz).1,p,hp,q,hq,r,hr,hpq,hqr,hrp,hB,
    mul_negative_of_opposite hopp (interior_side_positive B hpB hqB ht hpq hqt htp hz)⟩

private lemma across_nested {A B C : VertexTriple}
    (hAB : reflectionStep A.val B.val) (hCA : C ≠ A) : across B C ⊆ across A B := by
  obtain ⟨p,hp,q,hq,hpq,hB⟩ := hAB
  obtain ⟨r,hr,hqr,hrp,_⟩ := triangle_third_vertex A hp hq hpq
  have hpu := A.property.2 p hp
  have hqu := A.property.2 q hq
  have hfix := idealDiskSideReflection_endpoints hpu hqu hpq
  have hpB : p ∈ B.val := by rw [hB]; exact Finset.mem_image.mpr ⟨p,hp,hfix.1⟩
  have hqB : q ∈ B.val := by rw [hB]; exact Finset.mem_image.mpr ⟨q,hq,hfix.2⟩
  obtain ⟨t,ht,hqt,htp,_⟩ := triangle_third_vertex B hpB hqB hpq
  have hopp := reflected_reference_opposite A B hp hq hr hpq hqr hrp hB ht hqt htp
  rintro z ⟨hz,a,ha,b,hb,c,hc,hab,hbc,hca,hC,hneg⟩
  have hside : openSide a b ≠ openSide p q := by
    intro he
    have href := reflection_eq_of_side_eq (B.property.2 a ha) (B.property.2 b hb)
      hpu hqu hab hpq he
    have hback : A.val = reflectedVertices B.val p q := by
      have hcarr : triangle (reflectedVertices B.val p q) = triangle A.val := by
        rw [← idealDiskSideReflection_triangle_image_g6 B hpu hqu hpq hpB hqB,
          hB,← idealDiskSideReflection_triangle_image_g6 A hpu hqu hpq hp hq,
          Set.image_image]
        apply Set.Subset.antisymm
        · rintro w ⟨x,hx,rfl⟩
          simpa only [Function.comp_apply,
            idealDiskSideReflection_involutive_disk_g6 hpu hqu hpq x hx.1] using hx
        · intro w hw
          exact ⟨w,hw,idealDiskSideReflection_involutive_disk_g6 hpu hqu hpq w hw.1⟩
      let D : VertexTriple := ⟨_,reflected_vertices_triple B hpu hqu hpq⟩
      exact (congrArg Subtype.val (triangle_vertexTriple_injective (a₁ := D) hcarr)).symm
    apply hCA
    apply Subtype.ext
    rw [hC,hback]
    unfold reflectedVertices
    rw [href]
  have hpos := other_side_positive B ha hb hc hab hbc hca hpB hqB ht hpq hqt htp hside hz hneg
  exact ⟨hz,p,hp,q,hq,r,hr,hpq,hqr,hrp,hB,mul_negative_of_opposite hopp hpos⟩

private def reflectionGraph (V : VertexTriple) : SimpleGraph (ReachedTriangle V) where
  Adj A B := reflectionStep A.val.val B.val.val
  symm := ⟨fun _A _B h ↦ reflectionStep_symm h⟩
  loopless := ⟨fun _A h ↦ (reflectionStep_adjacent h).1 rfl⟩

private lemma reflectionGraph_connected (V : VertexTriple) : (reflectionGraph V).Connected := by
  have hreach (W : Finset ℂ) (hW : reachable V.val W) :
      (reflectionGraph V).Reachable (initialTriangle V)
        ⟨⟨W,reachable_preserves_vertexTriple V W hW⟩,hW⟩ := by
    induction hW with
    | refl => exact .refl _
    | @tail W U hW hWU ih =>
      exact ih.trans ((show (reflectionGraph V).Adj
        ⟨⟨W,reachable_preserves_vertexTriple V W hW⟩,hW⟩
        ⟨⟨U,reachable_preserves_vertexTriple V U (hW.tail hWU)⟩,hW.tail hWU⟩ from hWU).reachable)
  have : Nonempty (ReachedTriangle V) := ⟨initialTriangle V⟩
  exact SimpleGraph.Connected.mk fun A B ↦
    (hreach A.val.val A.property).symm.trans (hreach B.val.val B.property)

private lemma reflection_trail_across (V : VertexTriple) {B C : ReachedTriangle V}
    (P : (reflectionGraph V).Walk B C) :
    ∀ {A : ReachedTriangle V} (hAB : (reflectionGraph V).Adj A B),
      (SimpleGraph.Walk.cons hAB P).IsTrail → openTriangle C.val.val ⊆ across A.val B.val := by
  induction P with
  | nil =>
    intro A hAB htrail
    exact interior_subset_across hAB
  | @cons B D C hBD P ih =>
    intro A hAB htrail
    have hDA : D ≠ A := by
      intro he
      subst D
      have hn := (SimpleGraph.Walk.isTrail_cons hAB _).mp htrail |>.2
      apply hn
      simp only [SimpleGraph.Walk.edges_cons,List.mem_cons]
      exact Or.inl (Sym2.eq_swap)
    exact (ih hBD htrail.of_cons).trans
      (across_nested hAB (fun he ↦ hDA (Subtype.ext he)))

private lemma reflectionGraph_tree (V : VertexTriple) : (reflectionGraph V).IsTree := by
  refine ⟨reflectionGraph_connected V,?_⟩
  intro A P hcycle
  cases P with
  | nil => exact hcycle.ne_nil rfl
  | cons hAB P =>
    have hsub := reflection_trail_across V P hAB hcycle.isTrail
    obtain ⟨z,hz⟩ := normalized_triangle_carrier_nonempty_g6 A.val
    exact Set.disjoint_left.mp (across_disjoint_source A.val _)
      (interior_subset hz) (hsub hz)

private lemma reached_interiors_disjoint (V : VertexTriple) (A B : ReachedTriangle V)
    (hne : A ≠ B) : Disjoint (openTriangle A.val.val) (openTriangle B.val.val) := by
  classical
  obtain ⟨P⟩ := (reflectionGraph_connected V).preconnected A B
  let Q := P.toPath
  have hpath := Q.property
  obtain ⟨C,hAC,R,hQ⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne Q.val
  have ht : (SimpleGraph.Walk.cons hAC R).IsTrail := by rw [← hQ]; exact hpath.isTrail
  exact (across_disjoint_source A.val C.val).mono_left interior_subset |>.mono_right
    (reflection_trail_across V R hAC ht)

private lemma three_positive_mem_open {p q r z : ℂ}
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p) (hz : z ∈ disk)
    (h₁ : 0 < sideEquation p q z * sideEquation p q r)
    (h₂ : 0 < sideEquation q r z * sideEquation q r p)
    (h₃ : 0 < sideEquation r p z * sideEquation r p q) :
    z ∈ openTriangle {p,q,r} := by
  let U : Set ℂ := {w | w ∈ disk ∧ 0 < sideEquation p q w * sideEquation p q r ∧
    0 < sideEquation q r w * sideEquation q r p ∧ 0 < sideEquation r p w * sideEquation r p q}
  have ho : IsOpen U := (isOpen_lt continuous_norm continuous_const).inter
    ((isOpen_lt continuous_const ((continuous_sideEquation p q).mul_const _)).inter
      ((isOpen_lt continuous_const ((continuous_sideEquation q r).mul_const _)).inter
        (isOpen_lt continuous_const ((continuous_sideEquation r p).mul_const _))))
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (ho.mem_nhds (show z ∈ U from ⟨hz,h₁,h₂,h₃⟩))
  intro w hw
  exact (mem_triangle_three_iff hpq hqr hrp).mpr ⟨hw.1,hw.2.1.le,hw.2.2.1.le,hw.2.2.2.le⟩

private lemma carrier_subset_closure_interior (A : VertexTriple) :
    triangle A.val ⊆ closure (openTriangle A.val) := by
  intro z hz
  rcases triangle_subset_openTriangle_union_sides A.val hz with hzint | hzside
  · exact subset_closure hzint
  obtain ⟨p,hp,q,hq,hpq,hzside⟩ := hzside
  obtain ⟨r,hr,hqr,hrp,hA⟩ := triangle_third_vertex A hp hq hpq
  have hpu := A.property.2 p hp
  have hqu := A.property.2 q hq
  have hru := A.property.2 r hr
  let B : VertexTriple := ⟨reflectedVertices A.val p q,
    reflected_vertices_triple A hpu hqu hpq⟩
  have hfix := idealDiskSideReflection_endpoints hpu hqu hpq
  have hpB : p ∈ B.val := Finset.mem_image.mpr ⟨p,hp,hfix.1⟩
  have hqB : q ∈ B.val := Finset.mem_image.mpr ⟨q,hq,hfix.2⟩
  obtain ⟨t,ht,hqt,htp,_⟩ := triangle_third_vertex B hpB hqB hpq
  have hopp := reflected_reference_opposite A B hp hq hr hpq hqr hrp rfl ht hqt htp
  have htnon : sideEquation p q t ≠ 0 := by
    intro he
    rw [he,mul_zero] at hopp
    exact lt_irrefl 0 hopp
  have hzqr : sideEquation q r z ≠ 0 := by
    intro he
    have hd := openSide_disjoint_of_common_endpoint hqu hpu hru hpq.symm hqr hrp.symm
    exact Set.disjoint_left.mp hd (openSide_comm p q ▸ hzside) ⟨hz.1,he⟩
  have hzrp : sideEquation r p z ≠ 0 := by
    intro he
    have hd := openSide_disjoint_of_common_endpoint hpu hqu hru hpq hrp.symm hqr
    exact Set.disjoint_left.mp hd hzside (openSide_comm r p ▸ ⟨hz.1,he⟩)
  have hpnon : sideEquation q r p ≠ 0 := by
    intro he
    exact (eq_endpoint_of_sideEquation_eq_zero_unit hqu hru hpu he).elim hpq hrp.symm
  have hqnon : sideEquation r p q ≠ 0 := by
    intro he
    exact (eq_endpoint_of_sideEquation_eq_zero_unit hru hpu hqu he).elim hqr hpq.symm
  have h₂ : 0 < sideEquation q r z * sideEquation q r p :=
    lt_of_le_of_ne (hz.2 q hq r hr p hp hqr hrp hpq) (Ne.symm (mul_ne_zero hzqr hpnon))
  have h₃ : 0 < sideEquation r p z * sideEquation r p q :=
    lt_of_le_of_ne (hz.2 r hr p hp q hq hrp hpq hqr) (Ne.symm (mul_ne_zero hzrp hqnon))
  apply mem_closure_iff.mpr
  intro U hU hzU
  have hN : U ∩ {w | 0 < sideEquation q r w * sideEquation q r p} ∩
      {w | 0 < sideEquation r p w * sideEquation r p q} ∈ nhds z :=
    Filter.inter_mem (Filter.inter_mem (hU.mem_nhds hzU)
      ((isOpen_lt continuous_const ((continuous_sideEquation q r).mul_const _)).mem_nhds h₂))
      ((isOpen_lt continuous_const ((continuous_sideEquation r p).mul_const _)).mem_nhds h₃)
  obtain ⟨w,hw,hwD,hwneg⟩ := exists_negative_side_in_nhds hpu hqu hpq htnon hzside hN
  have h₁ : 0 < sideEquation p q w * sideEquation p q r := by
    rcases mul_neg_iff.mp hopp with ⟨hrpos,htneg⟩ | ⟨hrneg,htpos⟩
    · have hwpos : 0 < sideEquation p q w := by nlinarith
      exact mul_pos hwpos hrpos
    · have hwneg' : sideEquation p q w < 0 := by nlinarith
      exact mul_pos_of_neg_of_neg hwneg' hrneg
  refine ⟨w,hw.1.1,?_⟩
  rw [hA]
  exact three_positive_mem_open hpq hqr hrp hwD h₁ hw.1.2 hw.2

private lemma reached_carrier_disjoint_interior (V : VertexTriple)
    (A B : ReachedTriangle V) (hne : A ≠ B) :
    Disjoint (triangle A.val.val) (openTriangle B.val.val) :=
  ((reached_interiors_disjoint V A B hne).closure_left isOpen_interior).mono_left
    (carrier_subset_closure_interior A.val)

private lemma carrier_in_two_neighborhood (V : VertexTriple) (A B C : ReachedTriangle V)
    {z : ℂ} (hz : z ∈ triangle C.val.val)
    (hN : triangle A.val.val ∪ triangle B.val.val ∈ nhds z) : C = A ∨ C = B := by
  classical
  by_contra h
  push Not at h
  obtain ⟨U,hUN,hU,hzU⟩ := mem_nhds_iff.mp hN
  obtain ⟨w,hwU,hwC⟩ := mem_closure_iff.mp (carrier_subset_closure_interior C.val hz) U hU hzU
  rcases hUN hwU with hwA | hwB
  · exact Set.disjoint_left.mp (reached_carrier_disjoint_interior V A C h.1.symm) hwA hwC
  · exact Set.disjoint_left.mp (reached_carrier_disjoint_interior V B C h.2.symm) hwB hwC

private lemma reached_reflection_incidence (V : VertexTriple) (A : ReachedTriangle V)
    {p q : ℂ} (hp : p ∈ A.val.val) (hq : q ∈ A.val.val) (hpq : p ≠ q) :
    ∃ B : ReachedTriangle V, B.val.val = reflectedVertices A.val.val p q ∧ A ≠ B ∧
      hasSide B.val.val (openSide p q) ∧
      ∀ C : ReachedTriangle V, hasSide C.val.val (openSide p q) ↔ C = A ∨ C = B := by
  obtain ⟨B,hB,hne,hBS,hrest⟩ := reached_reflection_carriers V A hp hq hpq
  refine ⟨B,hB,hne,hBS,?_⟩
  intro C
  constructor
  · intro hCS
    have hn : (openSide p q).Nonempty := by
      by_contra he
      have hc := left_mem_closure_openSide (A.val.property.2 p hp) (A.val.property.2 q hq) hpq
      rw [Set.not_nonempty_iff_eq_empty.mp he,closure_empty] at hc
      exact hc
    obtain ⟨z,hz⟩ := hn
    obtain ⟨a,ha,b,hb,hab,hS⟩ := hCS
    have hzC := openSide_mem_triangle_of_vertexTriple C.val ha hb hab (hS ▸ hz)
    apply carrier_in_two_neighborhood V A B C hzC
    rw [hB]
    exact triangle_union_reflection_mem_nhds A.val hp hq hpq hz
  · rintro (rfl | rfl)
    · exact ⟨p,hp,q,hq,hpq,rfl⟩
    · exact hBS

private lemma reached_side_incidence (V : VertexTriple) (S : ReachedSide V) :
    ∃ A B : ReachedTriangle V, A ≠ B ∧ hasSide A.val.val S.val ∧ hasSide B.val.val S.val ∧
      ∀ C : ReachedTriangle V, hasSide C.val.val S.val ↔ C = A ∨ C = B := by
  obtain ⟨A,p,hp,q,hq,hpq,hS⟩ := S.property
  obtain ⟨B,hB,hne,hBS,hinc⟩ := reached_reflection_incidence V A hp hq hpq
  rw [hS]
  exact ⟨A,B,hne,⟨p,hp,q,hq,hpq,rfl⟩,hBS,hinc⟩

private lemma reflectionStep_iff_adjacent (V : VertexTriple) (A B : ReachedTriangle V) :
    reflectionStep A.val.val B.val.val ↔ (dualGraph V).Adj A B := by
  constructor
  · exact reflectionStep_adjacent
  · rintro ⟨hne,S,hAS,hBS⟩
    obtain ⟨p,hp,q,hq,hpq,rfl⟩ := hAS
    obtain ⟨C,hC,hAC,hCS,hinc⟩ := reached_reflection_incidence V A hp hq hpq
    rcases (hinc B).mp hBS with hBA | hBC
    · exact (hne (congrArg (fun X : ReachedTriangle V ↦ X.val.val) hBA.symm)).elim
    · rw [hBC,hC]
      exact ⟨p,hp,q,hq,hpq,rfl⟩

private lemma dualGraph_tree (V : VertexTriple) : (dualGraph V).IsTree := by
  have he : dualGraph V = reflectionGraph V := by
    ext A B
    exact (reflectionStep_iff_adjacent V A B).symm
  rw [he]
  exact reflectionGraph_tree V

private lemma reached_point_partition (V : VertexTriple) (z : disk) :
    ((∃! A : ReachedTriangle V, z.val ∈ openTriangle A.val.val) ∧
      ¬ ∃ S : ReachedSide V, z.val ∈ S.val) ∨
    ((∃! S : ReachedSide V, z.val ∈ S.val) ∧
      ¬ ∃ A : ReachedTriangle V, z.val ∈ openTriangle A.val.val) := by
  classical
  obtain ⟨A,hzA⟩ := reached_carriers_cover V z
  have hnotSide {B : ReachedTriangle V} (hzB : z.val ∈ openTriangle B.val.val) :
      ¬ ∃ S : ReachedSide V, z.val ∈ S.val := by
    rintro ⟨S,hzS⟩
    obtain ⟨C,p,hp,q,hq,hpq,hS⟩ := S.property
    have hzCS : z.val ∈ openSide p q := hS ▸ hzS
    have hzC := openSide_mem_triangle_of_vertexTriple C.val hp hq hpq hzCS
    by_cases hCB : C = B
    · subst C
      exact openSide_not_mem_openTriangle B.val hp hq hpq hzCS hzB
    · exact Set.disjoint_left.mp (reached_carrier_disjoint_interior V C B hCB) hzC hzB
  rcases triangle_subset_openTriangle_union_sides A.val.val hzA with hzI | hzS
  · refine Or.inl ⟨⟨A,hzI,?_⟩,hnotSide hzI⟩
    intro B hzB
    by_contra hBA
    exact Set.disjoint_left.mp (reached_interiors_disjoint V B A hBA) hzB hzI
  · obtain ⟨p,hp,q,hq,hpq,hzS⟩ := hzS
    let S : ReachedSide V := ⟨openSide p q,A,p,hp,q,hq,hpq,rfl⟩
    obtain ⟨B,hB,hne,hBS,hinc⟩ := reached_reflection_incidence V A hp hq hpq
    refine Or.inr ⟨⟨S,hzS,?_⟩,?_⟩
    · intro T hzT
      obtain ⟨C,hCT⟩ := T.property
      obtain ⟨a,ha,b,hb,hab,hT⟩ := hCT
      have hzC := openSide_mem_triangle_of_vertexTriple C.val ha hb hab (hT ▸ hzT)
      have hN : triangle A.val.val ∪ triangle B.val.val ∈ nhds z.val := by
        rw [hB]
        exact triangle_union_reflection_mem_nhds A.val hp hq hpq hzS
      rcases carrier_in_two_neighborhood V A B C hzC hN with rfl | rfl
      · apply Subtype.ext
        exact hasSide_point_unique C.val ⟨a,ha,b,hb,hab,hT⟩ ⟨p,hp,q,hq,hpq,rfl⟩ hzT hzS
      · apply Subtype.ext
        exact hasSide_point_unique C.val ⟨a,ha,b,hb,hab,hT⟩ hBS hzT hzS
    · rintro ⟨C,hzC⟩
      exact hnotSide hzC ⟨S,hzS⟩

private lemma reached_carrier_neighborhood_finite (V : VertexTriple) (z : disk) :
    ∃ U : Set ℂ, IsOpen U ∧ z.val ∈ U ∧
      {A : ReachedTriangle V | (U ∩ triangle A.val.val).Nonempty}.Finite := by
  classical
  obtain ⟨A,hzA⟩ := reached_carriers_cover V z
  rcases triangle_subset_openTriangle_union_sides A.val.val hzA with hzI | hzS
  · refine ⟨openTriangle A.val.val,isOpen_interior,hzI,?_⟩
    apply (Set.finite_singleton A).subset
    intro B hB
    obtain ⟨w,hwA,hwB⟩ := hB
    by_contra hne
    exact Set.disjoint_left.mp (reached_carrier_disjoint_interior V B A hne) hwB hwA
  · obtain ⟨p,hp,q,hq,hpq,hzS⟩ := hzS
    obtain ⟨B,hB,hne,hBS,hrest⟩ := reached_reflection_carriers V A hp hq hpq
    have hN : triangle A.val.val ∪ triangle B.val.val ∈ nhds z.val := by
      rw [hB]
      exact triangle_union_reflection_mem_nhds A.val hp hq hpq hzS
    obtain ⟨U,hUN,hU,hzU⟩ := mem_nhds_iff.mp hN
    refine ⟨U,hU,hzU,(Set.toFinite {A,B}).subset ?_⟩
    intro C hC
    obtain ⟨w,hwU,hwC⟩ := hC
    have hNw : triangle A.val.val ∪ triangle B.val.val ∈ nhds w :=
      Filter.mem_of_superset (hU.mem_nhds hwU) hUN
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using
      carrier_in_two_neighborhood V A B C hwC hNw

private lemma reached_triangles_locallyFinite (V : VertexTriple) :
    LocallyFinite (reachedTriangleFamily V) := by
  intro z
  obtain ⟨U,hU,hzU,hfinite⟩ := reached_carrier_neighborhood_finite V z
  refine ⟨Subtype.val ⁻¹' U, (hU.preimage continuous_subtype_val).mem_nhds hzU,?_⟩
  apply hfinite.subset
  intro A hA
  obtain ⟨w,hwA,hwU⟩ := hA
  exact ⟨w.val,hwU,hwA⟩

private lemma triangle_sides_finite (A : VertexTriple) :
    {S : Set ℂ | hasSide A.val S}.Finite := by
  classical
  have hf : (Set.range (fun x : A.val × A.val ↦ openSide x.1.val x.2.val)).Finite :=
    Set.finite_range _
  apply hf.subset
  rintro S ⟨p,hp,q,hq,hpq,rfl⟩
  exact ⟨(⟨p,hp⟩,⟨q,hq⟩),rfl⟩

private lemma reached_sides_locallyFinite (V : VertexTriple) :
    LocallyFinite (reachedSideFamily V) := by
  intro z
  obtain ⟨U,hU,hzU,hfinite⟩ := reached_carrier_neighborhood_finite V z
  refine ⟨Subtype.val ⁻¹' U, (hU.preimage continuous_subtype_val).mem_nhds hzU,?_⟩
  have hfside (A : ReachedTriangle V) : {S : ReachedSide V | hasSide A.val.val S.val}.Finite :=
    Set.Finite.preimage (f := fun S : ReachedSide V ↦ S.val)
      (fun _ _ _ _ h ↦ Subtype.ext h) (triangle_sides_finite A.val)
  have hfin := hfinite.biUnion (fun A _ ↦ hfside A)
  apply hfin.subset
  intro S hS
  obtain ⟨w,hwS,hwU⟩ := hS
  obtain ⟨A,p,hp,q,hq,hpq,hside⟩ := S.property
  apply Set.mem_iUnion.mpr ⟨A,?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨⟨w.val,hwU,?_⟩,⟨p,hp,q,hq,hpq,hside⟩⟩
  exact openSide_mem_triangle_of_vertexTriple A.val hp hq hpq (hside ▸ hwS)

private lemma side_ne_of_three {p q r : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hpq : p ≠ q) (_hqr : q ≠ r) (hrp : r ≠ p) : openSide p q ≠ openSide q r := by
  intro he
  have hc := left_mem_closure_openSide hp hq hpq
  rw [he] at hc
  have hz : sideEquation q r p = 0 := closure_minimal (fun _ h ↦ h.2)
    (isClosed_eq (continuous_sideEquation q r) continuous_const) hc
  exact (eq_endpoint_of_sideEquation_eq_zero_unit hq hr hp hz).elim hpq hrp.symm

private lemma reached_degree_three (V : VertexTriple) (A : ReachedTriangle V) :
    Nonempty (↥((dualGraph V).neighborSet A) ≃ Fin 3) := by
  classical
  obtain ⟨p,q,r,hpq,hpr,hqr,hA⟩ := Finset.card_eq_three.mp A.val.property.1
  have hp : p ∈ A.val.val := by rw [hA]; simp
  have hq : q ∈ A.val.val := by rw [hA]; simp
  have hr : r ∈ A.val.val := by rw [hA]; simp
  obtain ⟨B₁,hB₁,hne₁,hS₁,hi₁⟩ := reached_reflection_incidence V A hp hq hpq
  obtain ⟨B₂,hB₂,hne₂,hS₂,hi₂⟩ := reached_reflection_incidence V A hq hr hqr
  obtain ⟨B₃,hB₃,hne₃,hS₃,hi₃⟩ := reached_reflection_incidence V A hr hp hpr.symm
  have hpU := A.val.property.2 p hp
  have hqU := A.val.property.2 q hq
  have hrU := A.val.property.2 r hr
  have h₁₂ : B₁ ≠ B₂ := by
    intro he
    apply side_ne_of_three hpU hqU hrU hpq hqr hpr.symm
    exact sharedSide_unique (fun h ↦ hne₁ (Subtype.ext h))
      ⟨p,hp,q,hq,hpq,rfl⟩ hS₁ ⟨q,hq,r,hr,hqr,rfl⟩ (he ▸ hS₂)
  have h₂₃ : B₂ ≠ B₃ := by
    intro he
    apply side_ne_of_three hqU hrU hpU hqr hpr.symm hpq
    exact sharedSide_unique (fun h ↦ hne₂ (Subtype.ext h))
      ⟨q,hq,r,hr,hqr,rfl⟩ hS₂ ⟨r,hr,p,hp,hpr.symm,rfl⟩ (he ▸ hS₃)
  have h₃₁ : B₃ ≠ B₁ := by
    intro he
    apply side_ne_of_three hrU hpU hqU hpr.symm hpq hqr
    exact sharedSide_unique (fun h ↦ hne₃ (Subtype.ext h))
      ⟨r,hr,p,hp,hpr.symm,rfl⟩ hS₃ ⟨p,hp,q,hq,hpq,rfl⟩ (he ▸ hS₁)
  have he : (dualGraph V).neighborSet A = ({B₁,B₂,B₃} : Set (ReachedTriangle V)) := by
    ext C
    constructor
    · rintro ⟨hne,S,hAS,hCS⟩
      have hcne : C ≠ A := fun h ↦ hne (congrArg (fun X : ReachedTriangle V ↦ X.val.val) h.symm)
      have hc₁ : hasSide C.val.val (openSide p q) → C = B₁ :=
        fun h ↦ ((hi₁ C).mp h).resolve_left hcne
      have hc₂ : hasSide C.val.val (openSide q r) → C = B₂ :=
        fun h ↦ ((hi₂ C).mp h).resolve_left hcne
      have hc₃ : hasSide C.val.val (openSide r p) → C = B₃ :=
        fun h ↦ ((hi₃ C).mp h).resolve_left hcne
      obtain ⟨a,ha,b,hb,hab,rfl⟩ := hAS
      simp only [hA,Finset.mem_insert,Finset.mem_singleton] at ha hb
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first | exact (hab rfl).elim | exact Or.inl (hc₁ hCS) |
          exact Or.inr (Or.inl (hc₂ hCS)) | exact Or.inr (Or.inr (hc₃ hCS)) |
          (rw [openSide_comm] at hCS; first | exact Or.inl (hc₁ hCS) |
            exact Or.inr (Or.inl (hc₂ hCS)) | exact Or.inr (Or.inr (hc₃ hCS)))
    · intro hC
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hC
      rcases hC with rfl | rfl | rfl
      · exact (reflectionStep_iff_adjacent V A C).mp ⟨p,hp,q,hq,hpq,hB₁⟩
      · exact (reflectionStep_iff_adjacent V A C).mp ⟨q,hq,r,hr,hqr,hB₂⟩
      · exact (reflectionStep_iff_adjacent V A C).mp ⟨r,hr,p,hp,hpr.symm,hB₃⟩
  let F : Finset (ReachedTriangle V) := {B₁,B₂,B₃}
  have hF : (↑F : Set (ReachedTriangle V)) = (dualGraph V).neighborSet A := by
    rw [he]
    simp [F]
  have hcF : F.card = 3 := by simp [F,h₁₂,h₂₃,h₃₁.symm]
  exact ⟨(Set.equivOfEq hF.symm).trans (Finset.equivFinOfCardEq hcF)⟩

/-- The literal ideal-triangle reflection tiling of the open unit disk. (Epstein–Petronio, Thm. 5.5; Lyubich, Ex. 2.49(i)) -/
theorem reflection_tiling (V : VertexTriple) :
    Function.Injective (fun A : VertexTriple ↦ triangle A.val) ∧
    (∀ W : Finset ℂ, reachable V.val W → W.card = 3 ∧ ∀ p ∈ W, ‖p‖ = 1) ∧
    (∀ A : VertexTriple,
      (openTriangle A.val).Nonempty ∧
        triangle A.val = openTriangle A.val ∪
          {z | ∃ p ∈ A.val, ∃ q ∈ A.val, p ≠ q ∧ z ∈ openSide p q}) ∧
    (∀ A B : ReachedTriangle V, A ≠ B →
      Disjoint (openTriangle A.val.val) (openTriangle B.val.val)) ∧
    (∀ z : disk,
      ((∃! A : ReachedTriangle V, z.val ∈ openTriangle A.val.val) ∧
        ¬ ∃ S : ReachedSide V, z.val ∈ S.val) ∨
      ((∃! S : ReachedSide V, z.val ∈ S.val) ∧
        ¬ ∃ A : ReachedTriangle V, z.val ∈ openTriangle A.val.val)) ∧
    (∀ S : ReachedSide V,
      ∃ A B : ReachedTriangle V, A ≠ B ∧
        hasSide A.val.val S.val ∧ hasSide B.val.val S.val ∧
        ∀ C : ReachedTriangle V, hasSide C.val.val S.val ↔ C = A ∨ C = B) ∧
    LocallyFinite (reachedTriangleFamily V) ∧ LocallyFinite (reachedSideFamily V) ∧
    (dualGraph V).IsTree ∧
    (∀ A : ReachedTriangle V, Nonempty (↥((dualGraph V).neighborSet A) ≃ Fin 3)) ∧
    (∀ A B : ReachedTriangle V, (dualGraph V).Adj A B →
      ∃! S : ReachedSide V, hasSide A.val.val S.val ∧ hasSide B.val.val S.val) ∧
    (∀ A B : ReachedTriangle V,
      reflectionStep A.val.val B.val.val ↔ (dualGraph V).Adj A B) ∧
    (∀ A : ReachedTriangle V, ∀ p ∈ A.val.val, ∀ q ∈ A.val.val, p ≠ q →
      ∃ B : ReachedTriangle V,
        B.val.val = reflectedVertices A.val.val p q ∧ A ≠ B ∧
        hasSide B.val.val (openSide p q) ∧
        (∀ z ∈ openSide p q, idealDiskSideReflection p q z = z) ∧
        idealDiskSideReflection p q '' disk = disk ∧
        (∀ z ∈ disk, idealDiskSideReflection p q (idealDiskSideReflection p q z) = z) ∧
        idealDiskSideReflection p q '' triangle A.val.val = triangle B.val.val ∧
        idealDiskSideReflection p q '' triangle B.val.val = triangle A.val.val ∧
        (∀ C : ReachedTriangle V,
          hasSide C.val.val (openSide p q) ↔ C = A ∨ C = B)) ∧
    (∀ W : ReachedTriangle V,
      (∃! P : (dualGraph V).Walk (initialTriangle V) W, P.IsPath) ∧
        ∃ L : List (Finset ℂ), isSimpleItinerary V.val W.val.val L ∧
          (∀ K : List (Finset ℂ), isSimpleItinerary V.val W.val.val K → K = L) ∧
          (∀ K : List (Finset ℂ), isItinerary V.val W.val.val K → reducesItinerary K L) ∧
          ∀ P : (dualGraph V).Walk (initialTriangle V) W, P.IsPath →
            P.support.map (fun A ↦ A.val.val) = L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact triangle_vertexTriple_injective
  · exact reachable_preserves_vertexTriple V
  · intro A
    refine ⟨?_, Set.Subset.antisymm (triangle_subset_openTriangle_union_sides A.val) ?_⟩
    · exact normalized_triangle_carrier_nonempty_g6 A
    · intro z hz
      rcases hz with hz | hz
      · exact interior_subset hz
      · obtain ⟨p, hp, q, hq, hpq, hz⟩ := hz
        exact openSide_mem_triangle_of_vertexTriple A hp hq hpq hz
  · refine ⟨reached_interiors_disjoint V, reached_point_partition V, reached_side_incidence V,
      reached_triangles_locallyFinite V, reached_sides_locallyFinite V, dualGraph_tree V,
      reached_degree_three V, reached_adjacent_unique_side V, reflectionStep_iff_adjacent V, ?_,
      reflection_itinerary_normal_form_of_tree V (reachable_preserves_vertexTriple V)
        (reflectionStep_iff_adjacent V) (dualGraph_tree V)⟩
    intro A p hp q hq hpq
    obtain ⟨B,hB,hne,hBS,hfix,hdisk,hinv,himg,himg'⟩ :=
      reached_reflection_carriers V A hp hq hpq
    obtain ⟨C,hC,hneC,hCS,hinc⟩ := reached_reflection_incidence V A hp hq hpq
    have he : C = B := Subtype.ext (Subtype.ext (hC.trans hB.symm))
    subst C
    exact ⟨B,hB,hne,hBS,hfix,hdisk,hinv,himg,himg',hinc⟩

end HolomorphicAnosov.IdealDiskTriangle

