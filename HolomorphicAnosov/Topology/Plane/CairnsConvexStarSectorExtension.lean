import HolomorphicAnosov.Topology.CairnsPolygonAmbientExtension
import HolomorphicAnosov.Topology.AccumulatingChordArcClassification
import HolomorphicAnosov.Analysis.UnitCircleChordBoundaryZeroDeterminant
import HolomorphicAnosov.Topology.OrderedContactGapPairs
import HolomorphicAnosov.Topology.OpenAffineHullInteriorPositive
import HolomorphicAnosov.Topology.PathConcatenationContactOrder
import HolomorphicAnosov.Topology.WhyburnEmbeddedPathTransExact
import HolomorphicAnosov.Topology.CairnsCaseIIFrontIdentification
import HolomorphicAnosov.Topology.CairnsTargetRadialStarExtension
import HolomorphicAnosov.Topology.CompactRadialSweepHomeomorph
import HolomorphicAnosov.Topology.IntervalLoopCircleEmbedding
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Subpath
import HolomorphicAnosov.Topology.AccumulatingChordContinuity
import HolomorphicAnosov.Topology.HalfSectorConvexFront
import HolomorphicAnosov.Topology.Plane.CairnsChordSectorSeparation
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Defs

/-!
# Cairns's original convex-front star and its prescribed boundary extension

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
§3, Cases I/II and (D,E), printed pp.862–863, and §4(4.1),(4.2),(A), pp.863–864.
The original ordinary convex hull and complementary boundary arc are retained.
The supporting compact-hull and face arguments in the DAG use Gallier–Quaintance,
*Aspects of Convex Geometry*, author notes dated 9 October 2025, pp.65–67,99,
and Rockafellar, *Convex Analysis* (1970), §§7,9,10,18. These do not replace
Cairns's sector by a convex sector or assume its radial/contact conclusions.

All local definitions below are explicit notation for the constructions already
specified in this node. They neither bundle the theorem's conclusions into a
predicate nor postulate a geometric object. The plane is the native complex
plane, with its usual Euclidean norm, topology and real affine segments.
-/

namespace HolomorphicAnosov

open Set

/-- A complementary component of a closed endpoint-containing contact set on an embedded
interval is exactly an open parameter interval with contact endpoints. Agent expansion of
Cairns (1951), §3(D,E), pp.862–863. Take the last contact before and first contact after the
point by compact extrema. The image of the interval is connected and avoids contacts.
Conversely, a component crossing either endpoint would contain that contact by interval
connectedness of its preimage, a contradiction. -/
theorem embedded_interval_contact_gap {X : Type*} [TopologicalSpace X] [T2Space X]
    (q : unitInterval → X) (hq : Topology.IsEmbedding q)
    (C : Set X) (hC : IsClosed C) (h0 : q 0 ∈ C) (h1 : q 1 ∈ C)
    (x : X) (hx : x ∈ range q \ C) :
    ∃ l r : unitInterval, l < r ∧ q l ∈ C ∧ q r ∈ C ∧
      (∀ t : unitInterval, l < t → t < r → q t ∉ C) ∧
      connectedComponentIn (range q \ C) x = q '' Ioo l r := by
  obtain ⟨t, rfl⟩ := hx.1
  let F : Set ℝ := Subtype.val '' (q ⁻¹' C)
  have hFc : IsClosed F :=
    (isCompact_univ.of_isClosed_subset (hC.preimage hq.continuous) (subset_univ _)).image
      continuous_subtype_val |>.isClosed
  have hFsub : F ⊆ Icc (0 : ℝ) 1 := by
    rintro z ⟨u, hu, rfl⟩
    exact u.property
  have hF0 : (0 : ℝ) ∈ F := ⟨0, h0, rfl⟩
  have hF1 : (1 : ℝ) ∈ F := ⟨1, h1, rfl⟩
  have htF : (t : ℝ) ∉ F := by
    rintro ⟨u, hu, he⟩
    exact hx.2 (Subtype.ext he ▸ hu)
  obtain ⟨l, r, hl, hr, hlt, htr, hgap⟩ :=
    exists_closed_contact_gap F hFc hFsub hF0 hF1 t.property htF
  let a : unitInterval := ⟨l, hFsub hl⟩
  let b : unitInterval := ⟨r, hFsub hr⟩
  have ha : q a ∈ C := by
    obtain ⟨u, hu, he⟩ := hl
    exact (show u = a from Subtype.ext he) ▸ hu
  have hb : q b ∈ C := by
    obtain ⟨u, hu, he⟩ := hr
    exact (show u = b from Subtype.ext he) ▸ hu
  have hab : a < b := hlt.trans htr
  have hav : ∀ u : unitInterval, a < u → u < b → q u ∉ C := by
    intro u hau hub hu
    exact disjoint_left.mp hgap ⟨hau, hub⟩ ⟨u, hu, rfl⟩
  refine ⟨a, b, hab, ha, hb, hav, ?_⟩
  let K := connectedComponentIn (range q \ C) (q t)
  have hKsub : K ⊆ range q \ C := connectedComponentIn_subset _ _
  have hpre : IsPreconnected (q ⁻¹' K) := by
    apply hq.isInducing.isPreconnected_image.mp
    rw [image_preimage_eq_of_subset (hKsub.trans sdiff_subset)]
    exact isPreconnected_connectedComponentIn
  have htK : t ∈ q ⁻¹' K := mem_connectedComponentIn hx
  apply subset_antisymm
  · intro y hy
    obtain ⟨u, rfl⟩ := (hKsub hy).1
    refine ⟨u, ⟨?_, ?_⟩, rfl⟩
    · by_contra hua
      have haK := hpre.Icc_subset hy htK ⟨le_of_not_gt hua, hlt.le⟩
      exact (hKsub haK).2 ha
    · by_contra hbu
      have hbK := hpre.Icc_subset htK hy ⟨htr.le, le_of_not_gt hbu⟩
      exact (hKsub hbK).2 hb
  · apply (isPreconnected_Ioo.image q hq.continuous.continuousOn).subset_connectedComponentIn
      ⟨t, ⟨hlt, htr⟩, rfl⟩
    rintro y ⟨u, hu, rfl⟩
    exact ⟨⟨u, rfl⟩, hav u hu.1 hu.2⟩

/-- A specified contact-free parameter interval is a whole complementary component.
The connected interval lies in the component. Pulling the component back through the
embedding makes it order-convex, so it cannot pass either retained endpoint. -/
theorem embedded_interval_gap_component {X : Type*} [TopologicalSpace X] [T2Space X]
    (q : unitInterval → X) (hq : Topology.IsEmbedding q) (C : Set X)
    (l r t : unitInterval) (hl : q l ∈ C) (hr : q r ∈ C)
    (hgap : ∀ u : unitInterval, l < u → u < r → q u ∉ C)
    (ht : t ∈ Ioo l r) :
    connectedComponentIn (range q \ C) (q t) = q '' Ioo l r := by
  let K := connectedComponentIn (range q \ C) (q t)
  have hKsub : K ⊆ range q \ C := connectedComponentIn_subset _ _
  have hpre : IsPreconnected (q ⁻¹' K) := by
    apply hq.isInducing.isPreconnected_image.mp
    rw [image_preimage_eq_of_subset (hKsub.trans sdiff_subset)]
    exact isPreconnected_connectedComponentIn
  have htK : t ∈ q ⁻¹' K := mem_connectedComponentIn ⟨⟨t, rfl⟩, hgap t ht.1 ht.2⟩
  apply subset_antisymm
  · intro y hy
    obtain ⟨u, rfl⟩ := (hKsub hy).1
    refine ⟨u, ⟨?_, ?_⟩, rfl⟩
    · by_contra hul
      exact (hKsub (hpre.Icc_subset hy htK ⟨le_of_not_gt hul, ht.1.le⟩)).2 hl
    · by_contra hru
      exact (hKsub (hpre.Icc_subset htK hy ⟨ht.2.le, le_of_not_gt hru⟩)).2 hr
  · apply (isPreconnected_Ioo.image q hq.continuous.continuousOn).subset_connectedComponentIn
      ⟨t, ht, rfl⟩
    rintro y ⟨u, hu, rfl⟩
    exact ⟨⟨u, rfl⟩, hgap u hu.1 hu.2⟩

/-- If every point of a parameter gap lies on a contact-ended segment contained in the
noncontact locus, that whole gap is a straight open segment. The segment lies in the
component; its contact endpoints lie in the closure and hence are exactly the two gap
endpoints. The connected preimage of the closed segment contains the entire closed
parameter interval, giving the reverse inclusion. Cairns (1951), §3(E), p.863. -/
theorem embedded_interval_gap_segment
    (q : unitInterval → ℂ) (hq : Topology.IsEmbedding q) (C : Set ℂ)
    (l r : unitInterval) (hlr : l < r) (hl : q l ∈ C) (hr : q r ∈ C)
    (hgap : ∀ u : unitInterval, l < u → u < r → q u ∉ C)
    (hcover : ∀ x ∈ q '' Ioo l r, ∃ y z : ℂ, y ≠ z ∧ y ∈ C ∧ z ∈ C ∧
      x ∈ openSegment ℝ y z ∧ openSegment ℝ y z ⊆ range q \ C) :
    q '' Ioo l r = openSegment ℝ (q l) (q r) := by
  obtain ⟨t, hlt, htr⟩ := exists_between hlr
  obtain ⟨y, z, hyz, hyC, hzC, htx, hsub⟩ := hcover (q t) ⟨t, ⟨hlt, htr⟩, rfl⟩
  have hS : openSegment ℝ y z ⊆ q '' Ioo l r := by
    rw [← embedded_interval_gap_component q hq C l r t hl hr hgap ⟨hlt, htr⟩]
    exact (convex_openSegment y z).isPreconnected.subset_connectedComponentIn htx hsub
  have hcl : closure (q '' Ioo l r) = q '' Icc l r := by
    rw [hq.continuous.isClosedEmbedding hq.injective |>.closure_image_eq, closure_Ioo hlr.ne]
  have hend (v : ℂ) (hv : v ∈ C) (hvcl : v ∈ closure (q '' Ioo l r)) :
      v = q l ∨ v = q r := by
    rw [hcl] at hvcl
    obtain ⟨u, hu, rfl⟩ := hvcl
    by_cases hul : u = l
    · exact Or.inl (congrArg q hul)
    by_cases hur : u = r
    · exact Or.inr (congrArg q hur)
    exact False.elim (hgap u (lt_of_le_of_ne hu.1 (Ne.symm hul))
      (lt_of_le_of_ne hu.2 hur) hv)
  have hycl : y ∈ closure (q '' Ioo l r) :=
    closure_mono hS (segment_subset_closure_openSegment (left_mem_segment ℝ y z))
  have hzcl : z ∈ closure (q '' Ioo l r) :=
    closure_mono hS (segment_subset_closure_openSegment (right_mem_segment ℝ y z))
  have heq : openSegment ℝ y z = openSegment ℝ (q l) (q r) := by
    rcases hend y hyC hycl with hy | hy <;> rcases hend z hzC hzcl with hz | hz
    · exact False.elim (hyz (hy.trans hz.symm))
    · rw [hy, hz]
    · rw [hy, hz, openSegment_symm]
    · exact False.elim (hyz (hy.trans hz.symm))
  rw [heq] at hS
  have hclosed : IsClosed (range q) := (isCompact_range hq.continuous).isClosed
  have hsegsub : segment ℝ (q l) (q r) ⊆ range q := by
    rw [← closure_openSegment]
    exact closure_minimal (hS.trans (image_subset_range _ _)) hclosed
  have hpre : IsPreconnected (q ⁻¹' segment ℝ (q l) (q r)) := by
    apply hq.isInducing.isPreconnected_image.mp
    rw [image_preimage_eq_of_subset hsegsub]
    exact (convex_segment (q l) (q r)).isPreconnected
  refine subset_antisymm ?_ hS
  rintro w ⟨u, hu, rfl⟩
  apply mem_openSegment_of_ne_left_right (hq.injective.ne hu.1.ne)
    (hq.injective.ne hu.2.ne')
  exact hpre.Icc_subset (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _) ⟨hu.1.le, hu.2.le⟩

/-- The complementary components of a closed endpoint-containing contact set on an
embedded interval are countable. Their parameter preimages are nonempty pairwise disjoint
open intervals; second countability bounds their number. Cairns (1951), §3(E), p.863. -/
theorem embedded_interval_contact_components_countable
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (q : unitInterval → X) (hq : Topology.IsEmbedding q)
    (C : Set X) (hC : IsClosed C) (h0 : q 0 ∈ C) (h1 : q 1 ∈ C) :
    Set.Countable {K : Set X | ∃ x ∈ range q \ C,
      connectedComponentIn (range q \ C) x = K} := by
  apply Set.PairwiseDisjoint.countable_of_isOpen (s := fun K : Set X ↦ q ⁻¹' K)
  · intro K hK L hL hne
    apply Set.disjoint_left.mpr
    intro t htK htL
    obtain ⟨x, hx, rfl⟩ := hK
    obtain ⟨y, hy, rfl⟩ := hL
    exact hne ((connectedComponentIn_eq htK).trans (connectedComponentIn_eq htL).symm)
  · rintro K ⟨x, hx, rfl⟩
    obtain ⟨l, r, _, _, _, _, hgap⟩ := embedded_interval_contact_gap q hq C hC h0 h1 x hx
    rw [hgap, Set.preimage_image_eq _ hq.injective]
    exact isOpen_Ioo
  · rintro K ⟨x, hx, rfl⟩
    obtain ⟨t, rfl⟩ := hx.1
    exact ⟨t, mem_connectedComponentIn hx⟩


/-- A continuous path joining the antipodal endpoints of a closed semicircle covers it.
Apply the intermediate value theorem to the real coordinate after rotation; fixed norm and the
common sign determine the imaginary coordinate. Source: Cairns §4(A), elementary direction step. -/
theorem semicircle_path_surjective (W : ℂ) (hW : W ≠ 0) (c : ℝ) (hc : c ≠ 0)
    (q : unitInterval → Circle) (hq : Continuous q)
    (hside : ∀ t, 0 ≤ c * ((starRingEnd ℂ) W * (q t : ℂ)).im)
    (h0 : (q 0 : ℂ) = -(W / (‖W‖ : ℂ)))
    (h1 : (q 1 : ℂ) = W / (‖W‖ : ℂ)) :
    ∀ v : Circle, 0 ≤ c * ((starRingEnd ℂ) W * (v : ℂ)).im → ∃ t, q t = v := by
  intro v hv
  have hn : 0 < ‖W‖ := norm_pos_iff.mpr hW
  have hnC : (‖W‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnorm (u : Circle) : ‖(starRingEnd ℂ) W * (u : ℂ)‖ = ‖W‖ := by simp
  have hend : (starRingEnd ℂ) W * (W / (‖W‖ : ℂ)) = (‖W‖ : ℂ) := by
    rw [← mul_div_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast
    field_simp
  let f : unitInterval → ℝ := fun t ↦ ((starRingEnd ℂ) W * (q t : ℂ)).re
  have hf : Continuous f := Complex.continuous_re.comp
    (continuous_const.mul (continuous_subtype_val.comp hq))
  have hf0 : f 0 = -‖W‖ := by dsimp [f]; rw [h0, mul_neg, hend]; simp
  have hf1 : f 1 = ‖W‖ := by dsimp [f]; rw [h1, hend]; simp
  have hvbound : ((starRingEnd ℂ) W * (v : ℂ)).re ∈ Icc (f 0) (f 1) := by
    rw [hf0, hf1]
    have hbound := Complex.abs_re_le_norm ((starRingEnd ℂ) W * (v : ℂ))
    rw [hnorm, abs_le] at hbound
    exact hbound
  obtain ⟨t, ht, htv⟩ := intermediate_value_Icc (show (0 : unitInterval) ≤ 1 from zero_le_one)
    hf.continuousOn hvbound
  have hnormsq (u : Circle) : ((starRingEnd ℂ) W * (u : ℂ)).re ^ 2 +
      ((starRingEnd ℂ) W * (u : ℂ)).im ^ 2 = ‖W‖ ^ 2 := by
    simpa only [Complex.normSq_apply, ← pow_two, hnorm] using
      Complex.normSq_eq_norm_sq ((starRingEnd ℂ) W * (u : ℂ))
  have hre : ((starRingEnd ℂ) W * (q t : ℂ)).re = ((starRingEnd ℂ) W * (v : ℂ)).re := htv
  have him : ((starRingEnd ℂ) W * (q t : ℂ)).im = ((starRingEnd ℂ) W * (v : ℂ)).im := by
    have hsq : ((starRingEnd ℂ) W * (q t : ℂ)).im ^ 2 = ((starRingEnd ℂ) W * (v : ℂ)).im ^ 2 := by
      have hqt := hnormsq (q t)
      rw [hre] at hqt
      linarith [hnormsq v]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
    · exact heq
    · have hs := hside t
      have hzero : c * ((starRingEnd ℂ) W * (v : ℂ)).im = 0 := by rw [heq] at hs; nlinarith
      have hz := (mul_eq_zero.mp hzero).resolve_left hc
      rw [heq, hz, neg_zero]
  refine ⟨t, Subtype.ext ?_⟩
  exact mul_left_cancel₀ (star_ne_zero.mpr hW) (Complex.ext hre him)

/-- Unique radial coordinates imply that distinct front points have distinct normalized directions.
Order their radii and compare the shorter point at radial parameters one and the ratio of radii.
Source: Cairns §3(D), radial uniqueness. -/
theorem radial_unique_normalization_injective
    (M : ℂ) (L : Set ℂ) (hM : ∀ Q ∈ L, Q ≠ M)
    (hunique : ∀ (Q R : L) (t : unitInterval),
      (Q : ℂ) = (1 - (t : ℝ)) • M + (t : ℝ) • (R : ℂ) → Q = R) :
    Set.InjOn (fun Q : ℂ ↦ (Q - M) / (‖Q - M‖ : ℂ)) L := by
  have hordered (Q R : L) (hle : ‖(Q : ℂ) - M‖ ≤ ‖(R : ℂ) - M‖)
      (heq : ((Q : ℂ) - M) / (‖(Q : ℂ) - M‖ : ℂ) =
        ((R : ℂ) - M) / (‖(R : ℂ) - M‖ : ℂ)) : Q = R := by
    have hQn : 0 < ‖(Q : ℂ) - M‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hM _ Q.property))
    have hRn : 0 < ‖(R : ℂ) - M‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hM _ R.property))
    have hQnC : (‖(Q : ℂ) - M‖ : ℂ) ≠ 0 := by exact_mod_cast hQn.ne'
    have hRnC : (‖(R : ℂ) - M‖ : ℂ) ≠ 0 := by exact_mod_cast hRn.ne'
    let t : unitInterval := ⟨‖(Q : ℂ) - M‖ / ‖(R : ℂ) - M‖,
      (div_pos hQn hRn).le, (div_le_one hRn).mpr hle⟩
    apply hunique Q R t
    have hmul := (div_eq_div_iff hQnC hRnC).mp heq
    dsimp [t]
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div]
    field_simp
    linear_combination hmul
  intro Q hQ R hR heq
  rcases le_total ‖Q-M‖ ‖R-M‖ with hle | hle
  · exact congrArg Subtype.val (hordered ⟨Q,hQ⟩ ⟨R,hR⟩ hle heq)
  · exact congrArg Subtype.val (hordered ⟨R,hR⟩ ⟨Q,hQ⟩ hle heq.symm).symm

/-- A compact parametrized front with injective normalized direction and the endpoint/side
conditions has its normalized-direction homeomorphism onto the full closed semicircle.
The inverse radius is continuous and positive. Source: Cairns §3(D) and §4(A). -/
theorem compact_front_semicircle_homeomorph
    (W M : ℂ) (hW : W ≠ 0) (c : ℝ) (hc : c ≠ 0)
    (L : Set ℂ) (hL : IsCompact L) (q : unitInterval ≃ₜ L)
    (hM : ∀ Q ∈ L, Q ≠ M)
    (hside : ∀ Q ∈ L, 0 ≤ c * ((starRingEnd ℂ) W * (Q - M)).im)
    (h0 : ((q 0 : ℂ) - M) / (‖(q 0 : ℂ) - M‖ : ℂ) = -(W / (‖W‖ : ℂ)))
    (h1 : ((q 1 : ℂ) - M) / (‖(q 1 : ℂ) - M‖ : ℂ) = W / (‖W‖ : ℂ))
    (hinj : Set.InjOn (fun Q : ℂ ↦ (Q - M) / (‖Q - M‖ : ℂ)) L) :
    ∃ d : L ≃ₜ {v : Circle | 0 ≤ c * ((starRingEnd ℂ) W * (v : ℂ)).im},
      (∀ Q : L, ((d Q : Circle) : ℂ) = ((Q : ℂ) - M) / (‖(Q : ℂ) - M‖ : ℂ)) ∧
      Continuous (fun v ↦ ‖(d.symm v : ℂ) - M‖) ∧
      ∀ v, 0 < ‖(d.symm v : ℂ) - M‖ := by
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hn (Q : L) : 0 < ‖(Q : ℂ) - M‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hM _ Q.property))
  let n : L → Circle := fun Q ↦ ⟨((Q : ℂ) - M) / (‖(Q : ℂ) - M‖ : ℂ), by
    change ((Q : ℂ) - M) / (‖(Q : ℂ) - M‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    rw [Metric.mem_sphere, dist_zero_right]
    simp [(hn Q).ne']⟩
  have hncont : Continuous n := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.sub continuous_const).div
      (Complex.continuous_ofReal.comp (continuous_subtype_val.sub continuous_const).norm)
      (fun Q ↦ by exact_mod_cast (hn Q).ne')
  have hnside (Q : L) : 0 ≤ c * ((starRingEnd ℂ) W * (n Q : ℂ)).im := by
    change 0 ≤ c * ((starRingEnd ℂ) W * (((Q : ℂ)-M) / (‖(Q : ℂ)-M‖ : ℂ))).im
    rw [← mul_div_assoc, Complex.div_ofReal_im, ← mul_div_assoc]
    exact div_nonneg (hside Q Q.property) (hn Q).le
  let f : L → {v : Circle | 0 ≤ c * ((starRingEnd ℂ) W * (v : ℂ)).im} :=
    fun Q ↦ ⟨n Q, hnside Q⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro Q R he
      apply Subtype.ext
      apply hinj Q.property R.property
      exact congrArg (fun v : {v : Circle | 0 ≤ c * ((starRingEnd ℂ) W * (v : ℂ)).im} ↦
        (v.val : ℂ)) he
    · intro v
      obtain ⟨t, ht⟩ := semicircle_path_surjective W hW c hc (n ∘ q)
        (hncont.comp q.continuous) (fun t ↦ hnside (q t)) h0 h1 v v.property
      exact ⟨q t, Subtype.ext ht⟩
  let d := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij)
    (hncont.subtype_mk hnside)
  refine ⟨d, fun _ ↦ rfl, ?_, ?_⟩
  · exact (continuous_subtype_val.comp d.symm.continuous).sub continuous_const |>.norm
  · intro v
    exact hn (d.symm v)

/-- A parameter subinterval of one of two complementary circle arcs is a proper open arc,
with exactly its endpoint frontier. Source: the elementary arc topology used in Cairns, §3. -/
theorem embedded_circle_arc_gap_data
    (α β : unitInterval → Circle) (hα : Topology.IsEmbedding α) (hβ : Continuous β)
    (hcover : range α ∪ range β = univ)
    (hmeet : range α ∩ range β = {α 0, α 1})
    (l r : unitInterval) (hlr : l < r) :
    IsOpen (α '' Ioo l r) ∧ IsConnected (α '' Ioo l r) ∧
      α '' Ioo l r ≠ univ ∧ frontier (α '' Ioo l r) = {α l, α r} := by
  have hcross {t : unitInterval} (ht : α t ∈ range β) : t = 0 ∨ t = 1 := by
    have hh : α t ∈ ({α 0, α 1} : Set Circle) := hmeet ▸ ⟨mem_range_self t, ht⟩
    rcases hh with hh | hh
    · exact Or.inl (hα.injective hh)
    · exact Or.inr (hα.injective hh)
  have hcompl : (α '' Ioo l r)ᶜ = (α '' Icc 0 l) ∪ (α '' Icc r 1) ∪ range β := by
    ext z
    constructor
    · intro hz
      have hzcover : z ∈ range α ∪ range β := hcover ▸ mem_univ z
      rcases hzcover with ⟨t, rfl⟩ | hzβ
      · by_cases htl : t ≤ l
        · exact Or.inl (Or.inl ⟨t, ⟨unitInterval.nonneg t, htl⟩, rfl⟩)
        · exact Or.inl (Or.inr ⟨t, ⟨le_of_not_gt (fun htr ↦ hz ⟨t, ⟨lt_of_not_ge htl, htr⟩, rfl⟩),
            unitInterval.le_one t⟩, rfl⟩)
      · exact Or.inr hzβ
    · rintro ((⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | hzβ) ⟨u, hu, he⟩
      · exact (not_lt_of_ge ht.2) (hα.injective he ▸ hu.1)
      · exact (not_lt_of_ge ht.1) (hα.injective he ▸ hu.2)
      · have huβ : α u ∈ range β := he.symm ▸ hzβ
        rcases hcross huβ with h0 | h1
        · exact (not_lt_of_ge (unitInterval.nonneg l)) (by simpa [h0] using hu.1)
        · exact (not_lt_of_ge (show r ≤ (1 : unitInterval) from r.property.2)) (by simpa [h1] using hu.2)
  have hopen : IsOpen (α '' Ioo l r) := by
    apply isClosed_compl_iff.mp
    rw [hcompl]
    exact (((isCompact_Icc.image hα.continuous).isClosed).union
      (isCompact_Icc.image hα.continuous).isClosed).union (isCompact_range hβ).isClosed
  have hleft : α l ∉ α '' Ioo l r := by
    rintro ⟨u, hu, he⟩
    exact hu.1.ne (hα.injective he).symm
  refine ⟨hopen, ?_, fun he ↦ hleft (he ▸ mem_univ _), ?_⟩
  · exact (isConnected_Ioo hlr).image α hα.continuous.continuousOn
  · rw [frontier, hopen.interior_eq,
      hα.continuous.isClosedEmbedding hα.injective |>.closure_image_eq, closure_Ioo hlr.ne]
    ext z
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hout⟩
      by_cases hul : u = l
      · exact Or.inl (congrArg α hul)
      by_cases hur : u = r
      · exact Or.inr (congrArg α hur)
      exact False.elim (hout ⟨u, ⟨lt_of_le_of_ne hu.1 (Ne.symm hul),
        lt_of_le_of_ne hu.2 hur⟩, rfl⟩)
    · rintro (rfl | rfl)
      · exact ⟨⟨l, ⟨le_rfl, hlr.le⟩, rfl⟩, hleft⟩
      · refine ⟨⟨r, ⟨hlr.le, le_rfl⟩, rfl⟩, ?_⟩
        rintro ⟨u, hu, he⟩
        exact hu.2.ne (hα.injective he)

/-- Distinct gaps between contacts cannot overlap: an endpoint of one would be a contact
strictly inside the other. Source: Cairns, §3(D). -/
theorem contact_parameter_gaps_pairwise (P : unitInterval → Prop) :
    {g : unitInterval × unitInterval | g.1 < g.2 ∧ P g.1 ∧ P g.2 ∧
      ∀ t, g.1 < t → t < g.2 → ¬ P t}.Pairwise
      (fun g h ↦ Disjoint (Ioo g.1 g.2) (Ioo h.1 h.2)) := by
  intro g hg h hh hne
  apply disjoint_left.mpr
  intro t htg hth
  have hl : g.1 = h.1 := by
    apply le_antisymm
    · by_contra hle
      exact hh.2.2.2 g.1 (lt_of_not_ge hle) (htg.1.trans hth.2) hg.2.1
    · by_contra hle
      exact hg.2.2.2 h.1 (lt_of_not_ge hle) (hth.1.trans htg.2) hh.2.1
  have hr : g.2 = h.2 := by
    apply le_antisymm
    · by_contra hle
      exact hg.2.2.2 h.2 (htg.1.trans hth.2) (lt_of_not_ge hle) hh.2.2.1
    · by_contra hle
      exact hh.2.2.2 g.2 (hth.1.trans htg.2) (lt_of_not_ge hle) hg.2.2.1
  exact hne (Prod.ext hl hr)

/-- Contact gaps are countable by second countability of the parameter interval. -/
theorem contact_parameter_gaps_countable (P : unitInterval → Prop) :
    Set.Countable {g : unitInterval × unitInterval | g.1 < g.2 ∧ P g.1 ∧ P g.2 ∧
      ∀ t, g.1 < t → t < g.2 → ¬ P t} := by
  apply Set.PairwiseDisjoint.countable_of_isOpen (s := fun g : unitInterval × unitInterval ↦ Ioo g.1 g.2)
  · exact contact_parameter_gaps_pairwise P
  · exact fun _ _ ↦ isOpen_Ioo
  · exact fun _ hg ↦ nonempty_Ioo.mpr hg.1


/-- The complementary circle arc together with all contact gaps forms the countable disjoint
open-arc family needed for Cairns's simultaneous affine chord extension (§3(D,E)). -/
theorem embedded_circle_contact_arc_family
    (α β : unitInterval → Circle) (hα : Topology.IsEmbedding α)
    (hβ : Topology.IsEmbedding β) (hcover : range α ∪ range β = univ)
    (h0 : β 0 = α 0) (h1 : β 1 = α 1)
    (hmeet : range α ∩ range β = {α 0, α 1}) (P : unitInterval → Prop) :
    let G := {g : unitInterval × unitInterval | g.1 < g.2 ∧ P g.1 ∧ P g.2 ∧
      ∀ t, g.1 < t → t < g.2 → ¬ P t}
    let A : Option G → Set Circle := fun i ↦ match i with
      | none => β '' Ioo 0 1
      | some g => α '' Ioo g.val.1 g.val.2
    let u : Option G → Circle := fun i ↦ match i with
      | none => α 0
      | some g => α g.val.1
    let v : Option G → Circle := fun i ↦ match i with
      | none => α 1
      | some g => α g.val.2
    Countable G ∧ (∀ i, IsOpen (A i) ∧ IsConnected (A i) ∧ A i ≠ univ ∧
      frontier (A i) = {u i, v i} ∧ u i ≠ v i) ∧
      Pairwise (fun i j ↦ Disjoint (A i) (A j)) := by
  dsimp only
  let G := {g : unitInterval × unitInterval | g.1 < g.2 ∧ P g.1 ∧ P g.2 ∧
    ∀ t, g.1 < t → t < g.2 → ¬ P t}
  have hcross (g : G) : Disjoint (β '' Ioo 0 1) (α '' Ioo g.val.1 g.val.2) := by
    apply disjoint_left.mpr
    rintro z ⟨t, ht, rfl⟩ ⟨s, hs, he⟩
    have hh : β t ∈ ({α 0, α 1} : Set Circle) :=
      hmeet ▸ ⟨⟨s, he⟩, mem_range_self t⟩
    rcases hh with he0 | he1
    · have ht0 : t = 0 := hβ.injective (he0.trans h0.symm)
      exact ht.1.ne ht0.symm
    · have ht1 : t = 1 := hβ.injective (he1.trans h1.symm)
      exact ht.2.ne ht1
  refine ⟨(contact_parameter_gaps_countable P).to_subtype, ?_, ?_⟩
  · intro i
    cases i with
    | none =>
      obtain ⟨ho, hc, hp, hf⟩ := embedded_circle_arc_gap_data β α hβ hα.continuous
        (union_comm _ _ ▸ hcover) (by rw [inter_comm, hmeet, h0, h1]) 0 1 (by norm_num)
      exact ⟨ho, hc, hp, by simpa [h0, h1] using hf, hα.injective.ne (by norm_num)⟩
    | some g =>
      obtain ⟨ho, hc, hp, hf⟩ := embedded_circle_arc_gap_data α β hα hβ.continuous
        hcover hmeet g.val.1 g.val.2 g.property.1
      exact ⟨ho, hc, hp, hf, hα.injective.ne g.property.1.ne⟩
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some g => exact hcross g
    | some g =>
      cases j with
      | none => exact (hcross g).symm
      | some h =>
        apply disjoint_left.mpr
        rintro z ⟨t, ht, rfl⟩ ⟨s, hs, he⟩
        have hst : s = t := hα.injective he
        exact (disjoint_left.mp (contact_parameter_gaps_pairwise P g.property h.property
          (fun he ↦ hij (congrArg some (Subtype.ext he)))) ht (hst ▸ hs))

/-- Contact-order matching transfers pairwise disjointness from parameter gaps to their
straight front chords. Source: Cairns, §3(D,E). -/
theorem matching_contact_gap_chords_disjoint
    (μ q : unitInterval → ℂ) (hμ : Function.Injective μ) (hq : Function.Injective q)
    (P Q : unitInterval → Prop)
    (hmatch : ∀ g : {g : unitInterval × unitInterval | g.1 < g.2 ∧ P g.1 ∧ P g.2 ∧
        ∀ t, g.1 < t → t < g.2 → ¬ P t},
      ∃ l r : unitInterval, l < r ∧ Q l ∧ Q r ∧
        (∀ t, l < t → t < r → ¬ Q t) ∧ q l = μ g.val.1 ∧ q r = μ g.val.2 ∧
        openSegment ℝ (μ g.val.1) (μ g.val.2) = q '' Ioo l r) :
    Pairwise (fun g h : {g : unitInterval × unitInterval | g.1 < g.2 ∧ P g.1 ∧ P g.2 ∧
      ∀ t, g.1 < t → t < g.2 → ¬ P t} ↦
      Disjoint (openSegment ℝ (μ g.val.1) (μ g.val.2))
        (openSegment ℝ (μ h.val.1) (μ h.val.2))) := by
  intro g h hne
  obtain ⟨l, r, hlr, hl, hr, hgap, hle, hre, he⟩ := hmatch g
  obtain ⟨l', r', hlr', hl', hr', hgap', hle', hre', he'⟩ := hmatch h
  rw [he, he']
  apply disjoint_left.mpr
  rintro z ⟨t, ht, rfl⟩ ⟨s, hs, hst⟩
  have hpair : (l,r) ≠ (l',r') := by
    intro hh
    have hll : l = l' := congrArg Prod.fst hh
    have hrr : r = r' := congrArg Prod.snd hh
    apply hne
    apply Subtype.ext
    exact Prod.ext (hμ (hle.symm.trans ((congrArg q hll).trans hle')))
      (hμ (hre.symm.trans ((congrArg q hrr).trans hre')))
  exact disjoint_left.mp (contact_parameter_gaps_pairwise Q
    ⟨hlr, hl, hr, hgap⟩ ⟨hlr', hl', hr', hgap'⟩ hpair) ht (hq hst ▸ hs)

/-- Restrict a skeleton homeomorphism to a compact front, retaining exactly the prescribed
boundary contacts. This is the compact-front transport in Cairns, §4(A). -/
theorem compact_front_skeleton_transport
    (c L X K Y : Set ℂ) (hL : IsCompact L) (hcX : c ⊆ X) (hLX : L ⊆ X)
    (h : c ≃ₜ K) (H : X ≃ₜ Y)
    (hh : ∀ (x : X) (hx : (x : ℂ) ∈ c), (H x : ℂ) = (h ⟨x,hx⟩ : ℂ)) :
    ∃ (ν : Set ℂ) (e : L ≃ₜ ν), IsCompact ν ∧
      (∀ Q : L, (e Q : ℂ) = (H ⟨Q,hLX Q.property⟩ : ℂ)) ∧
      ν ∩ K = Subtype.val '' h '' {x : c | (x : ℂ) ∈ L} := by
  let f : L → ℂ := fun Q ↦ H ⟨Q,hLX Q.property⟩
  have hf : Continuous f := continuous_subtype_val.comp
    (H.continuous.comp (continuous_subtype_val.subtype_mk _))
  have hfi : Function.Injective f := by
    intro Q R he
    have hh := H.injective (Subtype.ext he)
    exact Subtype.ext (congrArg (fun z : X ↦ (z : ℂ)) hh)
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  let e : L ≃ₜ range f := (hf.isClosedEmbedding hfi).isEmbedding.toHomeomorph
  refine ⟨range f,e,isCompact_range hf,fun _ ↦ rfl,?_⟩
  ext z
  constructor
  · rintro ⟨⟨Q,rfl⟩,hK⟩
    let x : c := h.symm ⟨f Q,hK⟩
    have he : (H ⟨x,hcX x.property⟩ : ℂ) = f Q := by
      rw [hh _ x.property]
      exact congrArg Subtype.val (h.apply_symm_apply ⟨f Q,hK⟩)
    have hxQ : (x : ℂ) = Q := congrArg (fun z : X ↦ (z : ℂ)) (H.injective (Subtype.ext he))
    refine ⟨h x,⟨x,?_,rfl⟩,?_⟩
    · change (x : ℂ) ∈ L
      rw [hxQ]
      exact Q.property
    · exact congrArg Subtype.val (h.apply_symm_apply ⟨f Q,hK⟩)
  · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨⟨⟨x,hx⟩,?_⟩,(h x).property⟩
    exact hh _ x.property
/-- An embedded circle arc lies on one closed side of its endpoint chord and strictly
on that side off the endpoints. Source: elementary circle-chord separation in Cairns §4(A). -/
theorem embedded_circle_arc_signed_side
    (b : unitInterval → Circle) (hb : Continuous b) (hbi : Function.Injective b) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (∀ t, 0 ≤ ε * ((starRingEnd ℂ) ((b 1 : ℂ) - b 0) * ((b t : ℂ) - b 0)).im) ∧
      ∀ t ∈ Ioo (0 : unitInterval) 1,
        0 < ε * ((starRingEnd ℂ) ((b 1 : ℂ) - b 0) * ((b t : ℂ) - b 0)).im := by
  let f : unitInterval → ℝ := fun t ↦
    ((starRingEnd ℂ) ((b 1 : ℂ) - b 0) * ((b t : ℂ) - b 0)).im
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hne : (b 0 : ℂ) ≠ b 1 := fun he ↦
    (show (0 : unitInterval) ≠ 1 by norm_num) (hbi (Circle.coe_injective he))
  have hzero : f 0 = 0 ∧ f 1 = 0 := by
    constructor
    · simp [f]
    · dsimp [f]
      rw [← Complex.normSq_eq_conj_mul_self]
      simp
  have hn : ∀ t ∈ Ioo (0 : unitInterval) 1, f t ≠ 0 := by
    intro t ht hz
    rcases Analysis.unit_circle_chord_boundary_zero_determinant
      (b 0) (b 1) (b t) hne (Circle.norm_coe _) (Circle.norm_coe _)
      (Circle.norm_coe _) hz with h0 | h1
    · exact ht.1.ne (hbi (Circle.coe_injective h0)).symm
    · exact ht.2.ne (hbi (Circle.coe_injective h1))
  let m : unitInterval := ⟨1/2, by norm_num, by norm_num⟩
  have hm : m ∈ Ioo (0 : unitInterval) 1 := by
    change (0 : ℝ) < 1/2 ∧ (1/2 : ℝ) < 1
    norm_num
  have he : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ t ∈ Ioo (0 : unitInterval) 1, 0 < ε*f t := by
    rcases lt_or_gt_of_ne (hn m hm) with hmneg | hmpos
    · refine ⟨-1, Or.inr rfl, ?_⟩
      intro t ht
      have htneg := isPreconnected_Ioo.gt_of_ne hf.continuousOn hn ⟨m,hm,hmneg⟩ ht
      linarith
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro t ht
      have htpos := isPreconnected_Ioo.lt_of_ne hf.continuousOn hn ⟨m,hm,hmpos⟩ ht
      simpa using htpos
  obtain ⟨ε,hε,he⟩ := he
  refine ⟨ε,hε,?_,he⟩
  intro t
  change 0 ≤ ε * f t
  by_cases ht0 : t = 0
  · simp only [ht0,hzero.1,mul_zero,le_refl]
  by_cases ht1 : t = 1
  · simp only [ht1,hzero.2,mul_zero,le_refl]
  exact (he t ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
    lt_of_le_of_ne t.property.2 ht1⟩).le
/-- A front contained in the unit disk, supported at every noncircular point by a
half-plane whose interior contains N, has unique directions from N. -/
theorem supporting_front_normalization_injective
    (S : Set ℂ) (N : ℂ) (hN : ‖N‖ < 1) (hS : ∀ Q ∈ S, ‖Q‖ ≤ 1)
    (hsupport : ∀ Q ∈ S, ‖Q‖ = 1 ∨ ∃ f : ℂ → ℝ,
      f Q = 0 ∧ 0 < f N ∧ (∀ R ∈ S, 0 ≤ f R) ∧
      ∀ (R : ℂ) (t : ℝ), f ((1-t) • N + t • R) = (1-t)*f N + t*f R) :
    (∀ Q ∈ S, Q ≠ N) ∧ Set.InjOn (fun Q : ℂ ↦ (Q-N)/(‖Q-N‖ : ℂ)) S := by
  have havoid : ∀ Q ∈ S, Q ≠ N := by
    intro Q hQ he
    rcases hsupport Q hQ with hn | ⟨f,hf,hp,_⟩
    · rw [he] at hn
      linarith
    · rw [he] at hf
      linarith
  refine ⟨havoid,radial_unique_normalization_injective N S havoid ?_⟩
  intro Q R t he
  have ht : (t : ℝ) = 1 := by
    by_contra ht
    have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 ht
    rcases hsupport Q Q.property with hnorm | ⟨f,hf,hp,hs,haff⟩
    · have hn : ‖(Q : ℂ)‖ ≤ (1-(t : ℝ))*‖N‖ + (t : ℝ)*‖(R : ℂ)‖ := by
        rw [he]
        apply (norm_add_le _ _).trans
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr t.property.2), abs_of_nonneg t.property.1]
      have hR := hS R R.property
      have htr : (t : ℝ)*‖(R : ℂ)‖ ≤ (t : ℝ) := by nlinarith [t.property.1]
      have hp : 0 < (1-(t : ℝ))*(1-‖N‖) := mul_pos (sub_pos.mpr htlt) (sub_pos.mpr hN)
      linarith
    · have hh := haff R (t : ℝ)
      rw [← he,hf] at hh
      have hnonneg : 0 ≤ (t : ℝ)*f R := mul_nonneg t.property.1 (hs R R.property)
      have hpos : 0 < (1-(t : ℝ))*f N := mul_pos (sub_pos.mpr htlt) hp
      linarith
  apply Subtype.ext
  simpa [ht] using he

/-- The complement of a proper open circle arc has a supporting affine functional:
it vanishes at the two endpoints and is strictly positive elsewhere on the complement. -/
theorem circle_open_arc_complement_support
    (s : Set Circle) (u v : Circle) (hs : IsOpen s) (hc : IsConnected s)
    (hf : frontier s = {u,v}) (huv : u ≠ v)
    (g : Circle → Circle) (hg : Continuous g) (hgi : Function.Injective g) :
    ∃ f : ℂ → ℝ, f (g u) = 0 ∧ f (g v) = 0 ∧
      (∀ x y : ℂ, ∀ t : ℝ, f ((1-t) • x + t • y) = (1-t)*f x + t*f y) ∧
      (∀ p ∉ s, 0 ≤ f (g p)) ∧
      ∀ p ∉ s, p ≠ u → p ≠ v → 0 < f (g p) := by
  have haux (a b : Circle) (hab : a ≠ b)
      (hpath : s = Circle.path b a '' Ioo 0 1) :
      ∃ f : ℂ → ℝ, f (g a) = 0 ∧ f (g b) = 0 ∧
        (∀ x y : ℂ, ∀ t : ℝ, f ((1-t) • x + t • y) = (1-t)*f x + t*f y) ∧
        (∀ p ∉ s, 0 ≤ f (g p)) ∧
        ∀ p ∉ s, p ≠ a → p ≠ b → 0 < f (g p) := by
    let q : unitInterval → Circle := fun t ↦ g (Circle.path a b t)
    have hq : Continuous q := hg.comp (Circle.path a b).continuous
    have hqi : Function.Injective q := hgi.comp (Circle.path_injective_of_ne hab)
    obtain ⟨ε,hε,hside,hstrict⟩ := embedded_circle_arc_signed_side q hq hqi
    let f : ℂ → ℝ := fun z ↦ ε * ((starRingEnd ℂ) ((g b : ℂ)-g a) * (z-g a)).im
    have hf0 : f (g a) = 0 := by simp [f]
    have hf1 : f (g b) = 0 := by
      dsimp [f]
      rw [← Complex.normSq_eq_conj_mul_self]
      simp
    have hrange : sᶜ = range (Circle.path a b) := by
      rw [hpath, ← Circle.compl_range_path hab, compl_compl]
    refine ⟨f,hf0,hf1,?_,?_,?_⟩
    · intro x y t
      simp only [f, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.smul_re, Complex.smul_im, smul_eq_mul]
      ring
    · intro p hp
      obtain ⟨t,rfl⟩ := hrange ▸ (show p ∈ sᶜ from hp)
      simpa [q,f] using hside t
    · intro p hp hpa hpb
      obtain ⟨t,rfl⟩ := hrange ▸ (show p ∈ sᶜ from hp)
      have ht0 : t ≠ 0 := fun he ↦ hpa (by simp [he])
      have ht1 : t ≠ 1 := fun he ↦ hpb (by simp [he])
      simpa [q,f] using hstrict t
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 ht1⟩
  rcases circle_arc_subset_directed_path s u v hs hc hf huv with hp | hp
  · have he := circle_arc_eq_directed_path s u v hs hc hf huv hp
    obtain ⟨f,hfv,hfu,ha,hn,hp⟩ := haux v u huv.symm he
    exact ⟨f,hfu,hfv,ha,hn,fun p hps hpu hpv ↦ hp p hps hpv hpu⟩
  · have he := circle_arc_eq_directed_path s v u hs hc
      (hf.trans (pair_comm u v)) huv.symm hp
    exact haux u v huv he

/-- A radial sweep from an interior disk point meets the unit circle precisely at
its front contacts. Source: the strict convexity argument in Cairns §4(A). -/
theorem unit_circle_contact_radial_sweep (S : Set ℂ) (N : ℂ) (hN : ‖N‖ < 1)
    (hS : ∀ Q ∈ S, ‖Q‖ ≤ 1) :
    range (fun z : Circle ↦ (z:ℂ)) ∩
      {z | ∃ Q ∈ S, ∃ t ∈ Icc (0:ℝ) 1, z = (1-t) • N+t • Q} =
      range (fun z : Circle ↦ (z:ℂ)) ∩ S := by
  ext z
  constructor
  · rintro ⟨hz,⟨Q,hQ,t,ht,he⟩⟩
    have hnorm : ‖z‖ = 1 := by obtain ⟨w,rfl⟩ := hz; exact Circle.norm_coe w
    have ht1 : t = 1 := by
      by_contra hn
      have hlt : t < 1 := lt_of_le_of_ne ht.2 hn
      have hbound : ‖z‖ ≤ (1-t)*‖N‖+t*‖Q‖ := by
        rw [he]
        apply (norm_add_le _ _).trans
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr ht.2),abs_of_nonneg ht.1]
      have hq := hS Q hQ
      have hmul : t*‖Q‖ ≤ t := by nlinarith [ht.1]
      have hp : 0 < (1-t)*(1-‖N‖) := mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hN)
      linarith
    have heq : z = Q := by simpa [ht1] using he
    exact ⟨hz,heq.symm ▸ hQ⟩
  · intro hz
    exact ⟨hz.1,z,hz.2,1,by simp,by simp⟩
/-- Specialization of closed-cover gluing to two ambient closed unions. -/
theorem closed_union_homeomorph_gluing (P Q U V : Set ℂ) (hP : IsClosed P) (hQ : IsClosed Q)
    (hU : IsClosed U) (hV : IsClosed V) (F : P ≃ₜ U) (G : Q ≃ₜ V)
    (hagree : ∀ x (hp : x ∈ P) (hq : x ∈ Q), (F ⟨x,hp⟩:ℂ) = G ⟨x,hq⟩)
    (hoverlap : ∀ x : P, (F x:ℂ) ∈ V ↔ (x:ℂ) ∈ Q) :
    ∃ H : ↥(P ∪ Q) ≃ₜ ↥(U ∪ V),
      (∀ x : ↥(P ∪ Q), ∀ hx : (x:ℂ) ∈ P, (H x:ℂ) = F ⟨x,hx⟩) ∧
      (∀ x : ↥(P ∪ Q), ∀ hx : (x:ℂ) ∈ Q, (H x:ℂ) = G ⟨x,hx⟩) := by
  let lift (A B : Set ℂ) (hAB : A ⊆ B) : A ≃ₜ {x : B | (x:ℂ) ∈ A} :=
    { toFun := fun x ↦ ⟨⟨x,hAB x.property⟩,x.property⟩
      invFun := fun x ↦ ⟨x.val.val,x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  let PP : Set ↥(P ∪ Q) := {x | (x:ℂ) ∈ P}
  let QQ : Set ↥(P ∪ Q) := {x | (x:ℂ) ∈ Q}
  let UU : Set ↥(U ∪ V) := {x | (x:ℂ) ∈ U}
  let VV : Set ↥(U ∪ V) := {x | (x:ℂ) ∈ V}
  let F' : PP ≃ₜ UU := (lift P (P∪Q) subset_union_left).symm.trans
    (F.trans (lift U (U∪V) subset_union_left))
  let G' : QQ ≃ₜ VV := (lift Q (P∪Q) subset_union_right).symm.trans
    (G.trans (lift V (U∪V) subset_union_right))
  obtain ⟨H,hF,hG⟩ := closed_cover_homeomorph_gluing PP QQ UU VV
    (hP.preimage continuous_subtype_val) (hQ.preimage continuous_subtype_val)
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
    (by ext x; exact ⟨fun _ ↦ mem_univ _,fun _ ↦ x.property⟩)
    (by ext x; exact ⟨fun _ ↦ mem_univ _,fun _ ↦ x.property⟩) F' G'
    (by intro x hxP hxQ; exact Subtype.ext (hagree x hxP hxQ))
    (fun x ↦ hoverlap ⟨x.val.val,x.property⟩)
  refine ⟨H,?_,?_⟩
  · intro x hx
    exact congrArg Subtype.val (hF ⟨x,hx⟩)
  · intro x hx
    exact congrArg Subtype.val (hG ⟨x,hx⟩)
end HolomorphicAnosov

namespace HolomorphicAnosov.Topology.Plane

open Set

namespace CairnsStar

abbrev I := Set.Icc (0 : ℝ) 1

/-- The original three-vertex closed triangle in Cairns §3, p.863. -/
def triangle (M P D : ℂ) : Set ℂ := convexHull ℝ {M, P, D}

/-- The original Case II ordinary hull; open/closed generators agree after
adjoining the entire base by the first-contact and chord hypotheses. -/
def halfHull (M P D : ℂ) (μ : Set ℂ) : Set ℂ :=
  convexHull ℝ ((μ ∩ triangle M P D) ∪ segment ℝ D P)

/-- Cairns's actual Case I base or Case II complementary hull-boundary arc.
The existing half-sector proof identifies the latter with its M-facing front. -/
noncomputable def halfFront (M P D : ℂ) (μ β : Set ℂ) : Set ℂ := by
  classical
  exact if interior (triangle M P D) ⊆ β then segment ℝ D P
  else closure (frontier (halfHull M P D μ) \ segment ℝ D P)

/-- The Case I open triangle or Case II component adjacent to M. The existing
half-sector argument identifies the entire displayed difference with that component. -/
noncomputable def halfStar (M P D : ℂ) (μ β : Set ℂ) : Set ℂ := by
  classical
  exact if interior (triangle M P D) ⊆ β then interior (triangle M P D)
  else interior (triangle M P D) \ halfHull M P D μ

/-- The closed angular semicircle on the side of D₁D₂ containing P. -/
def directions (D₁ D₂ P : ℂ) : Set Circle :=
  {v | 0 ≤ ((star (D₂ - D₁) * (P - D₁)).im) *
    ((star (D₂ - D₁) * (v : ℂ)).im)}

/-- Literal closed radial sweep, including its two endpoint rays and its center. -/
def sweep (M : ℂ) (L : Set ℂ) : Set ℂ :=
  {z | ∃ Q ∈ L, ∃ t ∈ I, z = (1 - t) • M + t • Q}

/-- The open radial star on the specified side, excluding the base rays. -/
def openStar (D₁ D₂ P M : ℂ) (L : Set ℂ) : Set ℂ :=
  {z | ∃ Q ∈ L, ∃ t ∈ Ioo (0 : ℝ) 1,
    z = (1 - t) • M + t • Q ∧
    0 < ((star (D₂ - D₁) * (P - D₁)).im) *
      ((star (D₂ - D₁) * (z - D₁)).im)}

/-- Oriented endpoint pairs of the contact-free parameter gaps of an actual arc. -/
def gapPairs (q : I → ℂ) (C : Set ℂ) : Set (ℂ × ℂ) :=
  {p | ∃ l r : I, l < r ∧ q l ∈ C ∧ q r ∈ C ∧
    (∀ t : I, l < t → t < r → q t ∉ C) ∧ p = (q l, q r)}

/-- Matching contact parameters and point equalities transports oriented gap pairs. -/
theorem gap_pairs_transport (q₁ q₂ r₁ r₂ : unitInterval → ℂ) (C D : Set ℂ)
    (hgap : gapPairs q₁ C = gapPairs q₂ C)
    (hc₁ : ∀ t, r₁ t ∈ D ↔ q₁ t ∈ C) (hc₂ : ∀ t, r₂ t ∈ D ↔ q₂ t ∈ C)
    (he : ∀ s t, q₁ s = q₂ t ↔ r₁ s = r₂ t) :
    gapPairs r₁ D = gapPairs r₂ D := by
  have hforward (q₁ q₂ r₁ r₂ : unitInterval → ℂ)
      (hgap : gapPairs q₁ C = gapPairs q₂ C)
      (hc₁ : ∀ t, r₁ t ∈ D ↔ q₁ t ∈ C) (hc₂ : ∀ t, r₂ t ∈ D ↔ q₂ t ∈ C)
      (he : ∀ s t, q₁ s = q₂ t ↔ r₁ s = r₂ t) :
      gapPairs r₁ D ⊆ gapPairs r₂ D := by
    rintro p ⟨l,r,hlr,hl,hr,hfree,rfl⟩
    have hsrc : (q₁ l,q₁ r) ∈ gapPairs q₁ C :=
      ⟨l,r,hlr,(hc₁ l).mp hl,(hc₁ r).mp hr,
        fun t hlt htr ht ↦ hfree t hlt htr ((hc₁ t).mpr ht),rfl⟩
    rw [hgap] at hsrc
    obtain ⟨u,v,huv,hu,hv,hfree',hpair⟩ := hsrc
    refine ⟨u,v,huv,(hc₂ u).mpr hu,(hc₂ v).mpr hv,
      fun t hut htv ht ↦ hfree' t hut htv ((hc₂ t).mp ht),?_⟩
    exact Prod.ext ((he l u).mp (congrArg Prod.fst hpair))
      ((he r v).mp (congrArg Prod.snd hpair))
  apply subset_antisymm
  · exact hforward q₁ q₂ r₁ r₂ hgap hc₁ hc₂ he
  · apply hforward q₂ q₁ r₂ r₁ hgap.symm hc₂ hc₁
    intro s t
    exact ⟨fun hh ↦ ((he t s).mp hh.symm).symm,
      fun hh ↦ ((he t s).mpr hh.symm).symm⟩

end CairnsStar

open CairnsStar

attribute [local irreducible] convexHull

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000 in
/--
The original half-sector convex fronts give a closed direction homeomorphism,
the complete ordered contact/gap correspondence, and the radial extension of
an arbitrary prescribed homeomorphism of the entire embedded circle.

The two original arcs are supplied as embedded intervals covering the circle
and meeting only at their endpoints. A sector means exactly a connected component
of the original complementary region with the open chord removed, labeled by its
boundary arc. No convexity, finite contact set, radial uniqueness or order property
is an input. The sign of the perpendicular ray and its first contact are outputs.
Case selection and both actual fronts are then given by the literal definitions
above. Contact order is expressed by the two original arc parameters. Equality of
the ordered gap endpoint sets, together with the component clauses, expresses the
full bijection of complementary components, including collinear/accumulating gaps.
The compact-front direction maps and radii use the original norm and include both
endpoint directions. The final homeomorphism has the actual radial formula and
agrees with the prescribed map on every point of the original circle.

Natural-language proof, following the node's six steps:

1. The bounded sector's selected normal ray has a first boundary contact P on
its labeled arc. Its open initial segment is in the sector. Apply chord separation
to the embedded circle made of the original chord and that arc, cut by MP. This
gives the two actual half-sectors and their near-M quadrant labels.

2. The Case I tests using the full sector and the labeled half-sector agree.
The triangle interior is convex and avoids the MP cut by the strict transverse
coordinate. Its midpoint vertex is in its closure: segments from that vertex to
any interior point approach it through the interior. Hence the near-midpoint
seed meets the labeled half-sector. Connectedness confines the entire interior
to that one of the two disjoint open components. The reverse inclusion follows
from half-sector containment. Thus the literal halfFront and halfStar definitions
in Case I are exactly the opposite base and the triangle interior.
On each half apply the original Case I/II convex-front theorem. In Case I
the front is the opposite base. In Case II its ordinary compact hull has the
complementary boundary front given by closure(frontier K minus the base), and
the component adjacent to M is exactly the open triangle minus K. Both have the
original positive continuous first-hit radius through their endpoints. Glue the
two half fronts at their common retained point P. Their direction intervals glue
at the normal direction, giving the full front and open star with the stated
frontier and unique closed radial sweep.

3. The half-front contact theorem gives the closed contact set, its original
endpoint order, and the full disjoint contact-free source-subarc/front-gap
correspondence. Pull the genuine disjoint source gaps and complementary curve
arc back to the original circle parameter. Apply the accumulating-chord theorem
to the prescribed arbitrary boundary homeomorphism. Its null-family estimate,
compact skeletons and continuous affine chord formulas give a single skeleton
homeomorphism H₀, and its restriction gives the actual target compact simple arc.

4. In the selected circle sector each ray from the chord midpoint meets the
circle arc once. Every proper selected gap misses the retained h(P), so its
endpoint angle difference is strictly less than π. Its chord misses the midpoint
and its angle varies strictly monotonically. Ordered retained points and chords
therefore fill each target direction once. Compactness upgrades the direction
bijection to a homeomorphism, and its radius is positive and continuous, including
both endpoint rays. This gives the target open star, frontier and closed sweep.

5. Each noncentral point has unique front point Q and scalar t. The source and
target direction inverses give continuity of these coordinates away from the
center. Radial interpolation is bijective. A positive minimum source radius m
and finite maximum target radius L give the bound L|z−M|/m at the center; the
reverse bound proves inverse continuity. The two half formulas agree at P and
the endpoint rays give the prescribed affine map on the whole base chord.

6. The original circle meets the closed star precisely in the retained contact
set, and the target circle meets its star in the prescribed image of that set.
Thus the radial and boundary maps agree on their overlap and give a bijection of
the two unions. Finite closed-piece continuity and compact-to-Hausdorff inversion
give the final homeomorphism. Neither a countable pasting assertion nor an
orientation restriction on h is used. The source nodes remain proof dependencies;
their existence is not used as an extra hypothesis of this statement.
-/
theorem cairns_convex_star_sector_extension
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (p q : Circle) (hpq : p ≠ q)
    (α α' : I → Circle) (hα : Topology.IsEmbedding α)
    (hα' : Topology.IsEmbedding α')
    (hα0 : α ⟨0, by simp⟩ = p) (hα1 : α ⟨1, by simp⟩ = q)
    (hα'0 : α' ⟨0, by simp⟩ = p) (hα'1 : α' ⟨1, by simp⟩ = q)
    (hCover : range α ∪ range α' = univ)
    (hMeet : range α ∩ range α' = {p, q})
    (a β : Set ℂ) (haNonempty : a.Nonempty) (haBounded : Bornology.IsBounded a)
    (haComponent : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (hChord : openSegment ℝ (σ p) (σ q) ⊆ a)
    (hβ : ∃ x ∈ a \ openSegment ℝ (σ p) (σ q),
      connectedComponentIn (a \ openSegment ℝ (σ p) (σ q)) x = β)
    (hFrontier : frontier β ⊆ segment ℝ (σ p) (σ q) ∪ σ '' range α)
    (h : (range σ) ≃ₜ Circle) :
    let c := range σ
    let μ := σ '' range α
    let D₁ := σ p
    let D₂ := σ q
    let M := (D₁ + D₂) / 2
    let E₁ : ℂ := h ⟨D₁, ⟨p, rfl⟩⟩
    let E₂ : ℂ := h ⟨D₂, ⟨q, rfl⟩⟩
    let N := (E₁ + E₂) / 2
    let k := range (fun z : Circle ↦ (z : ℂ))
    ∃ (ε τ : ℝ) (sP : I), (ε = 1 ∨ ε = -1) ∧ 0 < τ ∧
      0 < (sP : ℝ) ∧ (sP : ℝ) < 1 ∧
      let P := M + τ • (ε • (Complex.I * (D₂ - D₁)))
      P = σ (α sP) ∧
      (∀ t ∈ Ioo (0 : ℝ) τ, M + t • (ε • (Complex.I * (D₂ - D₁))) ∈ β) ∧
      let μ₁ := (fun t : I ↦ σ (α t)) '' {t : I | t ≤ sP}
      let μ₂ := (fun t : I ↦ σ (α t)) '' {t : I | sP ≤ t}
      let L := halfFront M P D₁ μ₁ β ∪ halfFront M P D₂ μ₂ β
      let B := halfStar M P D₁ μ₁ β ∪ halfStar M P D₂ μ₂ β ∪ openSegment ℝ M P
      let C := L ∩ c
      B.Nonempty ∧ IsOpen B ∧ B ⊆ β ∧
      frontier B = segment ℝ D₁ D₂ ∪ L ∧ IsCompact L ∧
      closure B = sweep M L ∧ B = openStar D₁ D₂ P M L ∧
      (∀ z ∈ closure B, z ≠ M →
        ∃! w : L × I, z = (1 - (w.2 : ℝ)) • M + (w.2 : ℝ) • (w.1 : ℂ)) ∧
      IsClosed C ∧ C ⊆ μ ∧ D₁ ∈ C ∧ D₂ ∈ C ∧ P ∈ C ∧
      c ∩ closure B = C ∧
      ∃ (qs : I ≃ₜ L), (qs ⟨0, by simp⟩ : ℂ) = D₁ ∧
        (qs ⟨1, by simp⟩ : ℂ) = D₂ ∧
        (∀ u v s t : I, σ (α u) ∈ C → σ (α v) ∈ C →
          (qs s : ℂ) = σ (α u) → (qs t : ℂ) = σ (α v) → (u ≤ v ↔ s ≤ t)) ∧
        gapPairs (fun t : I ↦ σ (α t)) C = gapPairs (fun t ↦ (qs t : ℂ)) C ∧
        (∀ l r : I, l < r → (qs l : ℂ) ∈ C → (qs r : ℂ) ∈ C →
          (∀ t : I, l < t → t < r → (qs t : ℂ) ∉ C) →
          (fun t : I ↦ (qs t : ℂ)) '' {t : I | l < t ∧ t < r} =
            openSegment ℝ (qs l : ℂ) (qs r : ℂ) ∧
          openSegment ℝ (qs l : ℂ) (qs r : ℂ) ⊆ a ∧
          Disjoint (openSegment ℝ (qs l : ℂ) (qs r : ℂ)) c) ∧
        (∀ x ∈ μ \ C, ∃ l r : I, l < r ∧ σ (α l) ∈ C ∧ σ (α r) ∈ C ∧
          (∀ t : I, l < t → t < r → σ (α t) ∉ C) ∧
          connectedComponentIn (μ \ C) x =
            (fun t : I ↦ σ (α t)) '' {t : I | l < t ∧ t < r}) ∧
        (∀ x ∈ L \ C, ∃ l r : I, l < r ∧ (qs l : ℂ) ∈ C ∧ (qs r : ℂ) ∈ C ∧
          (∀ t : I, l < t → t < r → (qs t : ℂ) ∉ C) ∧
          connectedComponentIn (L \ C) x =
            (fun t : I ↦ (qs t : ℂ)) '' {t : I | l < t ∧ t < r}) ∧
        Set.Countable {G : Set ℂ | ∃ x ∈ L \ C, connectedComponentIn (L \ C) x = G} ∧
        ∃ ds : L ≃ₜ directions D₁ D₂ P,
          (∀ Q : L, ((ds Q : Circle) : ℂ) = ((Q : ℂ) - M) / (‖(Q : ℂ) - M‖ : ℂ)) ∧
          Continuous (fun v : directions D₁ D₂ P ↦ ‖(ds.symm v : ℂ) - M‖) ∧
          (∀ v : directions D₁ D₂ P, 0 < ‖(ds.symm v : ℂ) - M‖) ∧
          ∃ (ν : Set ℂ) (H₀ : ↥(c ∪ segment ℝ D₁ D₂ ∪ L) ≃ₜ
            ↥(k ∪ segment ℝ E₁ E₂ ∪ ν)),
            H₀ '' {x | (x : ℂ) ∈ L} = {y | (y : ℂ) ∈ ν} ∧
            (∀ (x : ↥(c ∪ segment ℝ D₁ D₂ ∪ L)) (hx : (x : ℂ) ∈ c),
              (H₀ x : ℂ) = (h ⟨(x : ℂ), hx⟩ : ℂ)) ∧
            (∀ (x₁ x₂ : c) (t : I) (x : ↥(c ∪ segment ℝ D₁ D₂ ∪ L)),
              ((x₁ : ℂ), (x₂ : ℂ)) ∈ gapPairs (fun t ↦ (qs t : ℂ)) C →
              (x : ℂ) = (1 - (t : ℝ)) • (x₁ : ℂ) + (t : ℝ) • (x₂ : ℂ) →
              (H₀ x : ℂ) = (1 - (t : ℝ)) • (h x₁ : ℂ) + (t : ℝ) • (h x₂ : ℂ)) ∧
            (∀ (t : I) (x : ↥(c ∪ segment ℝ D₁ D₂ ∪ L)),
              (x : ℂ) = (1 - (t : ℝ)) • D₁ + (t : ℝ) • D₂ →
              (H₀ x : ℂ) = (1 - (t : ℝ)) • E₁ + (t : ℝ) • E₂) ∧
            let Eₚ : ℂ := h ⟨σ (α sP), ⟨α sP, rfl⟩⟩
            let Cν := Subtype.val '' h '' {x : c | (x : ℂ) ∈ C}
            let γ := openStar E₁ E₂ Eₚ N ν
            IsCompact ν ∧ ν ∩ k = Cν ∧
            γ.Nonempty ∧ IsOpen γ ∧ frontier γ = segment ℝ E₁ E₂ ∪ ν ∧
            closure γ = sweep N ν ∧
            γ ⊆ Metric.ball (0 : ℂ) 1 ∩
              {z | 0 < ((star (E₂ - E₁) * (Eₚ - E₁)).im) *
                ((star (E₂ - E₁) * (z - E₁)).im)} ∧
            (∀ z ∈ closure γ, z ≠ N →
              ∃! w : ν × I, z = (1 - (w.2 : ℝ)) • N + (w.2 : ℝ) • (w.1 : ℂ)) ∧
            ∃ qt : I ≃ₜ ν,
              (qt ⟨0, by simp⟩ : ℂ) = E₁ ∧ (qt ⟨1, by simp⟩ : ℂ) = E₂ ∧
              (∀ (t : I) (x : ↥(c ∪ segment ℝ D₁ D₂ ∪ L)),
                (x : ℂ) = (qs t : ℂ) → (H₀ x : ℂ) = (qt t : ℂ)) ∧
              gapPairs (fun t : I ↦ (h ⟨σ (α t), ⟨α t, rfl⟩⟩ : ℂ)) Cν =
                gapPairs (fun t ↦ (qt t : ℂ)) Cν ∧
              (∀ l r : I, l < r → (qt l : ℂ) ∈ Cν → (qt r : ℂ) ∈ Cν →
                (∀ t : I, l < t → t < r → (qt t : ℂ) ∉ Cν) →
                (fun t : I ↦ (qt t : ℂ)) '' {t : I | l < t ∧ t < r} =
                  openSegment ℝ (qt l : ℂ) (qt r : ℂ) ∧
                openSegment ℝ (qt l : ℂ) (qt r : ℂ) ⊆ Metric.ball (0 : ℂ) 1 ∧
                Disjoint (openSegment ℝ (qt l : ℂ) (qt r : ℂ)) k) ∧
              ∃ dt : ν ≃ₜ directions E₁ E₂ Eₚ,
                (∀ Q : ν, ((dt Q : Circle) : ℂ) =
                  ((Q : ℂ) - N) / (‖(Q : ℂ) - N‖ : ℂ)) ∧
                Continuous (fun v : directions E₁ E₂ Eₚ ↦ ‖(dt.symm v : ℂ) - N‖) ∧
                (∀ v : directions E₁ E₂ Eₚ, 0 < ‖(dt.symm v : ℂ) - N‖) ∧
                ∃ H : ↥(c ∪ closure B) ≃ₜ ↥(k ∪ closure γ),
                  (∀ (x : ↥(c ∪ closure B)) (hx : (x : ℂ) ∈ c),
                    (H x : ℂ) = (h ⟨(x : ℂ), hx⟩ : ℂ)) ∧
                  (∀ (Q : L) (t : I) (x : ↥(c ∪ closure B))
                    (y : ↥(c ∪ segment ℝ D₁ D₂ ∪ L)),
                    (y : ℂ) = (Q : ℂ) →
                    (x : ℂ) = (1 - (t : ℝ)) • M + (t : ℝ) • (Q : ℂ) →
                    (H x : ℂ) = (1 - (t : ℝ)) • N + (t : ℝ) • (H₀ y : ℂ)) := by
  classical
  -- Checked radial-extension stage, in the literal sweep coordinates used below.
  -- The preceding front geometry supplies its uniqueness and positive-radius guards.
  have hRadialExtension (L T : Set ℂ) (hL : IsCompact L) (M N : ℂ)
      (hM : ∀ Q ∈ L, Q ≠ M) (hN : ∀ Q ∈ T, Q ≠ N) (e : L ≃ₜ T)
      (hUniqueL : ∀ z ∈ sweep M L, z ≠ M →
        ∃! w : L × I, z = (1 - (w.2 : ℝ)) • M + (w.2 : ℝ) • (w.1 : ℂ))
      (hUniqueT : ∀ z ∈ sweep N T, z ≠ N →
        ∃! w : T × I, z = (1 - (w.2 : ℝ)) • N + (w.2 : ℝ) • (w.1 : ℂ)) :
      ∃ H : sweep M L ≃ₜ sweep N T, ∀ (Q : L) (t : I),
        (H ⟨(1 - (t : ℝ)) • M + (t : ℝ) • (Q : ℂ),
          ⟨Q, Q.property, t, t.property, rfl⟩⟩ : ℂ) =
          (1 - (t : ℝ)) • N + (t : ℝ) • (e Q : ℂ) := by
    have hrange (S : Set ℂ) (P : ℂ) : sweep P S =
        range (fun w : S × I ↦ (1 - (w.2 : ℝ)) • P + (w.2 : ℝ) • (w.1 : ℂ)) := by
      ext z
      constructor
      · rintro ⟨Q,hQ,t,ht,he⟩
        exact ⟨(⟨Q,hQ⟩,⟨t,ht⟩),he.symm⟩
      · rintro ⟨⟨Q,t⟩,rfl⟩
        exact ⟨Q,Q.property,t,t.property,rfl⟩
    have hinjective (S : Set ℂ) (P : ℂ) (hP : ∀ Q ∈ S, Q ≠ P)
        (hunique : ∀ z ∈ sweep P S, z ≠ P →
          ∃! w : S × I, z = (1 - (w.2 : ℝ)) • P + (w.2 : ℝ) • (w.1 : ℂ))
        (Q R : S) (t u : I) (ht : t ≠ 0)
        (he : (1 - (t : ℝ)) • P + (t : ℝ) • (Q : ℂ) =
          (1 - (u : ℝ)) • P + (u : ℝ) • (R : ℂ)) : Q = R ∧ t = u := by
      have hne : (1 - (t : ℝ)) • P + (t : ℝ) • (Q : ℂ) ≠ P := by
        intro hz
        have hsmul : (t : ℝ) • ((Q : ℂ) - P) = 0 := by
          calc
            _ = (1 - (t : ℝ)) • P + (t : ℝ) • (Q : ℂ) - P := by module
            _ = 0 := sub_eq_zero.mpr hz
        have ht0 : (t : ℝ) = 0 :=
          (smul_eq_zero.mp hsmul).resolve_right (sub_ne_zero.mpr (hP _ Q.property))
        exact ht (Subtype.ext ht0)
      have hmem : (1 - (t : ℝ)) • P + (t : ℝ) • (Q : ℂ) ∈ sweep P S :=
        ⟨Q,Q.property,t,t.property,rfl⟩
      have hpair : (Q,t) = (R,u) := (hunique _ hmem hne).unique rfl he
      exact ⟨congrArg Prod.fst hpair,congrArg Prod.snd hpair⟩
    obtain ⟨H,hH⟩ := HolomorphicAnosov.compact_radial_sweep_homeomorph
      L T hL M N hM hN e (hinjective L M hM hUniqueL) (hinjective T N hN hUniqueT)
    let eL := Homeomorph.setCongr (hrange L M)
    let eT := Homeomorph.setCongr (hrange T N)
    refine ⟨eL.trans (H.trans eT.symm), ?_⟩
    intro Q t
    exact hH Q t
  have hD : σ p ≠ σ q := hσ.injective.ne hpq
  have hcCompact : IsCompact (range σ) := isCompact_range hσ.continuous
  have haSub : a ⊆ (range σ)ᶜ := by
    obtain ⟨x, hx, he⟩ := haComponent
    rw [← he]
    exact connectedComponentIn_subset _ _
  have hβSub : β ⊆ a \ openSegment ℝ (σ p) (σ q) := by
    obtain ⟨x, hx, he⟩ := hβ
    rw [← he]
    exact connectedComponentIn_subset _ _
  have hβNonempty : β.Nonempty := by
    obtain ⟨x, hx, he⟩ := hβ
    exact he ▸ (connectedComponentIn_nonempty_iff.mpr hx)
  have hβConnected : IsConnected β := by
    obtain ⟨x, hx, he⟩ := hβ
    exact he ▸ (isConnected_connectedComponentIn_iff.mpr hx)
  have hβBounded : Bornology.IsBounded β := haBounded.subset (fun z hz ↦ (hβSub hz).1)
  obtain ⟨β₁, β₂, hne₁, hne₂, hconn₁, hconn₂, hopen₁, hopen₂, hdisj,
    hcover, hcomponents, hfront₁, hfront₂, hlocal⟩ :=
      HolomorphicAnosov.cairns_chord_sector_separation σ hσ p q hpq α α'
        hα hα' hα0 hα1 hα'0 hα'1 hCover hMeet a haNonempty haBounded
        haComponent hChord
  have hβChoice : β = β₁ ∨ β = β₂ := by
    obtain ⟨x, hx, he⟩ := hβ
    simpa only [he] using hcomponents x hx
  have hβOpen : IsOpen β := hβChoice.elim (fun he ↦ he ▸ hopen₁) (fun he ↦ he ▸ hopen₂)
  have hmid : (σ p + σ q) / 2 ∈ openSegment ℝ (σ p) (σ q) := by
    convert midpoint_mem_openSegment (𝕜 := ℝ) (σ p) (σ q) using 1
    simp only [midpoint_eq_smul_add, invOf_eq_inv, Complex.real_smul, Complex.ofReal_inv,
      Complex.ofReal_ofNat]
    ring
  have hβSide : ∃ r : ℝ, 0 < r ∧ Metric.ball ((σ p + σ q) / 2) r ⊆ a ∧
      ({z ∈ Metric.ball ((σ p + σ q) / 2) r |
        0 < (star (σ q - σ p) * (z - σ p)).im} ⊆ β ∨
      {z ∈ Metric.ball ((σ p + σ q) / 2) r |
        (star (σ q - σ p) * (z - σ p)).im < 0} ⊆ β) := by
    obtain ⟨r, hr, hball, hpos, hneg, hparts, hsides⟩ := hlocal _ hmid
    refine ⟨r, hr, hball, ?_⟩
    rcases hβChoice with rfl | rfl
    · exact hsides.elim (fun hs ↦ Or.inl hs.1) (fun hs ↦ Or.inr hs.2)
    · exact hsides.elim (fun hs ↦ Or.inr hs.2) (fun hs ↦ Or.inl hs.1)
  have hperpCross (t ε : ℝ) :
      (star (σ q - σ p) *
        ((σ p + σ q) / 2 + t • (ε • (Complex.I * (σ q - σ p))) - σ p)).im =
          t * ε * Complex.normSq (σ q - σ p) := by
    simp [Complex.mul_im, Complex.mul_re, Complex.normSq_apply,
      Complex.real_smul]
    ring
  have hβRay : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ δ : ℝ, 0 < δ ∧
      (∀ t ∈ Ioo (0 : ℝ) δ,
        (σ p + σ q) / 2 + t • (ε • (Complex.I * (σ q - σ p))) ∈ β) ∧
      ∃ r : ℝ, 0 < r ∧ Metric.ball ((σ p + σ q) / 2) r ⊆ a ∧
        {z ∈ Metric.ball ((σ p + σ q) / 2) r |
          0 < ε * (star (σ q - σ p) * (z - σ p)).im} ⊆ β := by
    obtain ⟨r, hr, hball, hsides⟩ := hβSide
    have hsign : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
        {z ∈ Metric.ball ((σ p + σ q) / 2) r |
          0 < ε * (star (σ q - σ p) * (z - σ p)).im} ⊆ β := by
      rcases hsides with hs | hs
      · exact ⟨1, Or.inl rfl, by simpa only [one_mul] using hs⟩
      · exact ⟨-1, Or.inr rfl, by simpa only [neg_one_mul, neg_pos] using hs⟩
    obtain ⟨ε, hε, hside⟩ := hsign
    have hcont : Continuous (fun t : ℝ ↦
        (σ p + σ q) / 2 + t • (ε • (Complex.I * (σ q - σ p)))) := by fun_prop
    obtain ⟨δ, hδ, hdist⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x := 0)) r hr
    refine ⟨ε, hε, δ, hδ, ?_, r, hr, hball, hside⟩
    intro t ht
    apply hside
    constructor
    · simpa only [Metric.mem_ball, zero_smul, add_zero] using
        hdist (by simpa [Real.dist_eq, abs_of_pos ht.1] using ht.2)
    · rw [hperpCross]
      have hn : 0 < Complex.normSq (σ q - σ p) :=
        Complex.normSq_pos.mpr (sub_ne_zero.mpr hD.symm)
      rcases hε with rfl | rfl <;> nlinarith [mul_pos ht.1 hn]
  obtain ⟨ε, hε, δ, hδ, hentry, r, hr, hball, hside⟩ := hβRay
  let M : ℂ := (σ p + σ q) / 2
  let V : ℂ := ε • (Complex.I * (σ q - σ p))
  let ray : ℝ → ℂ := fun t ↦ M + t • V
  have hV : V ≠ 0 := by
    rcases hε with rfl | rfl <;> simp [V, mul_ne_zero Complex.I_ne_zero
      (sub_ne_zero.mpr hD.symm)]
  have hnV : 0 < ‖V‖ := norm_pos_iff.mpr hV
  have hcont : Continuous ray := by dsimp [ray]; fun_prop
  have hescape : ∃ T : ℝ, δ / 2 ≤ T ∧ ray T ∉ β := by
    obtain ⟨R, hR, hbound⟩ := hβBounded.exists_pos_norm_le
    let T := δ + (R + ‖M‖ + 1) / ‖V‖
    have hT : 0 < T := by dsimp [T]; positivity
    have hTδ : δ / 2 ≤ T := by
      have hp : 0 < (R + ‖M‖ + 1) / ‖V‖ := by positivity
      dsimp [T]
      linarith
    refine ⟨T, hTδ, ?_⟩
    intro hmem
    have hb := hbound (ray T) hmem
    have hi : ‖T • V‖ ≤ ‖ray T‖ + ‖M‖ := by
      simpa [ray] using norm_sub_le (ray T) M
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hT] at hi
    have he : T * ‖V‖ = δ * ‖V‖ + R + ‖M‖ + 1 := by
      dsimp [T]
      field_simp
      ring
    nlinarith [mul_pos hδ hnV]
  let S : Set ℝ := {t | δ / 2 ≤ t ∧ ray t ∉ β}
  have hSclosed : IsClosed S := isClosed_Ici.inter (hβOpen.isClosed_compl.preimage hcont)
  have hSne : S.Nonempty := hescape
  have hSbelow : BddBelow S := ⟨δ / 2, fun t ht ↦ ht.1⟩
  obtain ⟨τ, hτS, hτMin⟩ : ∃ τ : ℝ, τ ∈ S ∧ ∀ t ∈ S, τ ≤ t :=
    ⟨sInf S, hSclosed.csInf_mem hSne hSbelow, fun t ht ↦ csInf_le hSbelow ht⟩
  have hτ : 0 < τ := lt_of_lt_of_le (by positivity : 0 < δ / 2) hτS.1
  have hray : ∀ t ∈ Ioo (0 : ℝ) τ, ray t ∈ β := by
    intro t ht
    by_cases htδ : t < δ
    · exact hentry t ⟨ht.1, htδ⟩
    · by_contra hnot
      have htS : t ∈ S := ⟨by linarith, hnot⟩
      exact (not_le_of_gt ht.2) (hτMin t htS)
  have hcontact : ray τ ∈ frontier β := by
    rw [hβOpen.frontier_eq]
    refine ⟨?_, hτS.2⟩
    apply hcont.continuousWithinAt.mem_closure (s := Ioo (0 : ℝ) τ) _ hray
    rw [closure_Ioo hτ.ne]
    exact ⟨hτ.le, le_rfl⟩
  have hchordCross (z : ℂ) (hz : z ∈ segment ℝ (σ p) (σ q)) :
      (star (σ q - σ p) * (z - σ p)).im = 0 := by
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    have hae : a = 1 - b := by linarith
    rw [hae]
    simp [Complex.mul_im, Complex.mul_re, Complex.real_smul]
    ring
  have hcrossNe : (star (σ q - σ p) * (ray τ - σ p)).im ≠ 0 := by
    change (star (σ q - σ p) *
      ((σ p + σ q) / 2 + τ • (ε • (Complex.I * (σ q - σ p))) - σ p)).im ≠ 0
    rw [hperpCross]
    have hεne : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
    exact mul_ne_zero (mul_ne_zero hτ.ne' hεne)
      (Complex.normSq_pos.mpr (sub_ne_zero.mpr hD.symm)).ne'
  have hnotbase : ray τ ∉ segment ℝ (σ p) (σ q) :=
    fun hz ↦ hcrossNe (hchordCross _ hz)
  obtain ⟨u, ⟨sP, rfl⟩, hP⟩ := (hFrontier hcontact).resolve_left hnotbase
  have hs0 : 0 < (sP : ℝ) := by
    by_contra hn
    have hs : sP = ⟨0, by simp⟩ := Subtype.ext (by linarith [sP.property.1])
    have he : ray τ = σ p := by simpa only [hs, hα0] using hP.symm
    exact hnotbase (he ▸ left_mem_segment ℝ (σ p) (σ q))
  have hs1 : (sP : ℝ) < 1 := by
    by_contra hn
    have hs : sP = ⟨1, by simp⟩ := Subtype.ext (by linarith [sP.property.2])
    have he : ray τ = σ q := by simpa only [hs, hα1] using hP.symm
    exact hnotbase (he ▸ right_mem_segment ℝ (σ p) (σ q))
  let μ : Path (σ p) (σ q) :=
    { toFun := fun t ↦ σ (α t)
      continuous_toFun := hσ.continuous.comp hα.continuous
      source' := congrArg σ hα0
      target' := congrArg σ hα1 }
  have hμInjective : Function.Injective μ := hσ.injective.comp hα.injective
  have hμCurve : range μ ⊆ range σ := by
    rintro z ⟨t, rfl⟩
    exact ⟨α t, rfl⟩
  have hμContact : μ sP = ray τ := hP
  have hfirstContact : ∀ t ∈ Ioo (0 : ℝ) 1,
      M + t • (μ sP - M) ∉ range σ := by
    intro t ht
    have htr : 0 < t * τ ∧ t * τ < τ :=
      ⟨mul_pos ht.1 hτ, by nlinarith [ht.2]⟩
    have hz := haSub (hβSub (hray (t * τ) htr)).1
    simpa only [hμContact, ray, add_sub_cancel_left, smul_smul, Set.mem_compl_iff] using hz
  have hperpendicular :
      (μ sP - M).re * (σ q - σ p).re +
        (μ sP - M).im * (σ q - σ p).im = 0 := by
    rw [hμContact]
    simp [ray, V, Complex.real_smul, Complex.mul_re, Complex.mul_im]
    ring
  let chord : Path (σ q) (σ p) := Path.segment (σ q) (σ p)
  have hchordInjective : Function.Injective chord := Path.segment_injective_of_ne hD.symm
  have havoid (u v : I) (hv0 : 0 < (v : ℝ)) (hv1 : (v : ℝ) < 1) :
      μ u ≠ chord v := by
    have hm : chord v ∈ openSegment ℝ (σ q) (σ p) :=
      lineMap_mem_openSegment ℝ (σ q) (σ p) ⟨hv0, hv1⟩
    rw [openSegment_symm] at hm
    intro he
    exact haSub (hChord hm) (he ▸ hμCurve ⟨u, rfl⟩)
  let loop : Path (σ p) (σ p) := μ.trans chord
  have hloopInjective : InjOn loop.extend (Ico (0 : ℝ) 1) := by
    intro x hx y hy he
    rw [Path.extend_apply loop ⟨hx.1, hx.2.le⟩,
      Path.extend_apply loop ⟨hy.1, hy.2.le⟩] at he
    simp only [loop, Path.trans_apply] at he
    split_ifs at he with hxh hyh hyh
    · have he' := congrArg Subtype.val (hμInjective he)
      dsimp at he'
      linarith
    · exact False.elim (havoid _ _ (by dsimp; linarith) (by dsimp; linarith [hx.2, hy.2]) he)
    · exact False.elim (havoid _ _ (by dsimp; linarith) (by dsimp; linarith [hx.2, hy.2]) he.symm)
    · have he' := congrArg Subtype.val (hchordInjective he)
      dsimp at he'
      linarith
  obtain ⟨σ₀, hσ₀, hσ₀range⟩ :=
    HolomorphicAnosov.Topology.intervalLoop_circle_embedding loop.extend
      loop.continuous_extend.continuousOn (by simp) hloopInjective
  have hcircleRange : range σ₀ = segment ℝ (σ p) (σ q) ∪ σ '' range α := by
    rw [hσ₀range, Path.image_extend_of_subset loop subset_rfl, Path.trans_range,
      Path.range_segment, segment_symm]
    have hμrange : range μ = σ '' range α := by
      change range (σ ∘ α) = σ '' range α
      exact range_comp σ α
    rw [hμrange, union_comm]
  have hβOutside : β ⊆ (range σ₀)ᶜ := by
    intro z hz hzcurve
    have hznot : z ∉ range σ := haSub (hβSub hz).1
    rw [hcircleRange] at hzcurve
    rcases hzcurve with hzseg | ⟨t, ht, he⟩
    · have hpz : σ p ≠ z := by rintro rfl; exact hznot ⟨p, rfl⟩
      have hqz : σ q ≠ z := by rintro rfl; exact hznot ⟨q, rfl⟩
      exact (hβSub hz).2 (mem_openSegment_of_ne_left_right hpz hqz hzseg)
    · exact hznot ⟨t, he⟩
  have hβNewComponent : ∃ x ∈ β, connectedComponentIn (range σ₀)ᶜ x = β := by
    obtain ⟨x, hx⟩ := hβNonempty
    refine ⟨x, hx, ?_⟩
    let F := connectedComponentIn (range σ₀)ᶜ x
    have hxF : x ∈ F := mem_connectedComponentIn (hβOutside hx)
    have hFsub : F ⊆ (range σ₀)ᶜ := connectedComponentIn_subset _ _
    have hfrontDisj : Disjoint (frontier β) F := by
      apply Set.disjoint_left.mpr
      intro z hzfront hzF
      apply hFsub hzF
      rw [hcircleRange]
      exact hFrontier hzfront
    have : PreconnectedSpace F := Subtype.preconnectedSpace isPreconnected_connectedComponentIn
    have hclopen : IsClopen ((Subtype.val : F → ℂ) ⁻¹' β) :=
      isClopen_preimage_val hβOpen hfrontDisj
    have hfull := hclopen.eq_univ ⟨⟨x, hxF⟩, hx⟩
    apply Subset.antisymm
    · intro z hz
      have hm : (⟨z, hz⟩ : F) ∈ (Subtype.val : F → ℂ) ⁻¹' β := by
        rw [hfull]
        trivial
      exact hm
    · exact hβConnected.isPreconnected.subset_connectedComponentIn hx hβOutside
  have hMcurve : M ∈ range σ₀ := by
    rw [hcircleRange]
    exact Or.inl (openSegment_subset_segment ℝ (σ p) (σ q) hmid)
  have hPcurve : μ sP ∈ range σ₀ := by
    rw [hcircleRange]
    exact Or.inr ⟨α sP, ⟨sP, rfl⟩, rfl⟩
  obtain ⟨pM, hpM⟩ := hMcurve
  obtain ⟨pP, hpP⟩ := hPcurve
  have hMPne : M ≠ μ sP := by
    intro he
    apply hnotbase
    rw [← hμContact, ← he]
    exact openSegment_subset_segment ℝ (σ p) (σ q) hmid
  have hpMP : pM ≠ pP := fun he ↦ hMPne (hpM.symm.trans ((congrArg σ₀ he).trans hpP))
  have hMPchord : openSegment ℝ M (μ sP) ⊆ β := by
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    have hbt : 0 < b * τ ∧ b * τ < τ := ⟨mul_pos hb hτ, by nlinarith⟩
    have he : a • M + b • μ sP = ray (b * τ) := by
      rw [hμContact]
      dsimp [ray]
      have habc : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
      push_cast
      calc
        _ = ((a : ℂ) + (b : ℂ)) * M + ((b : ℂ) * (τ : ℂ)) * V := by ring
        _ = _ := by rw [habc, one_mul]
    rw [he]
    exact hray _ hbt
  -- The two concrete boundary arcs start along MD_i and return along μ_i.
  have hhalfInterior (i : I) (hi : i = 0 ∨ i = 1) (t : I) (ht : (t : ℝ) < 1) :
      Path.segment M (μ i) t ∈ openSegment ℝ (σ p) (σ q) := by
    rcases hi with rfl | rfl
    · refine ⟨(1 + (t : ℝ)) / 2, (1 - (t : ℝ)) / 2,
        by linarith [t.property.1], by linarith, by ring, ?_⟩
      simp [Path.segment, AffineMap.lineMap_apply_module, M, Complex.real_smul]
      ring
    · refine ⟨(1 - (t : ℝ)) / 2, (1 + (t : ℝ)) / 2,
        by linarith, by linarith [t.property.1], by ring, ?_⟩
      simp [Path.segment, AffineMap.lineMap_apply_module, M, Complex.real_smul]
      ring
  let ρ (i : I) : Path M (μ sP) := (Path.segment M (μ i)).trans (μ.subpath i sP)
  have hρInjective (i : I) (hi : i = 0 ∨ i = 1) : Function.Injective (ρ i) := by
    have his : (i : ℝ) ≠ (sP : ℝ) := by
      rcases hi with rfl | rfl
      · exact hs0.ne
      · exact hs1.ne'
    have hMi : M ≠ μ i := by
      intro he
      apply haSub (hChord hmid)
      change M ∈ range σ
      rw [he]
      exact hμCurve ⟨i, rfl⟩
    have hseg := Path.segment_injective_of_ne hMi
    have hsub : Function.Injective (μ.subpath i sP) := by
      intro x y he
      have hv := congrArg Subtype.val (hμInjective he)
      change (1 - (x : ℝ)) * i + x * sP = (1 - (y : ℝ)) * i + y * sP at hv
      apply Subtype.ext
      have hf : ((x : ℝ) - y) * ((i : ℝ) - sP) = 0 := by nlinarith only [hv]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right (sub_ne_zero.mpr his))
    have hcross (u v : I) (hv : 0 < (v : ℝ)) :
        Path.segment M (μ i) u ≠ μ.subpath i sP v := by
      intro he
      by_cases hu : (u : ℝ) < 1
      · have hm := hhalfInterior i hi u hu
        apply haSub (hChord hm)
        rw [he]
        exact hμCurve ⟨Icc.convexComb i sP v, rfl⟩
      · have hu1 : u = 1 := by
          apply Subtype.ext
          change (u : ℝ) = 1
          linarith [u.property.2]
        rw [hu1, Path.target] at he
        have he' := congrArg Subtype.val (hμInjective he)
        change (i : ℝ) = (1 - (v : ℝ)) * i + v * sP at he'
        have hf : (v : ℝ) * ((i : ℝ) - sP) = 0 := by nlinarith only [he']
        exact (mul_ne_zero hv.ne' (sub_ne_zero.mpr his)) hf
    intro x y he
    simp only [ρ, Path.trans_apply] at he
    split_ifs at he with hx hy hy
    · apply Subtype.ext
      have hv := congrArg Subtype.val (hseg he)
      dsimp at hv
      linarith
    · exact False.elim (hcross _ _ (by dsimp; linarith) he)
    · exact False.elim (hcross _ _ (by dsimp; linarith) he.symm)
    · apply Subtype.ext
      have hv := congrArg Subtype.val (hsub he)
      dsimp at hv
      linarith
  have hρRange (i : I) : range (ρ i) = segment ℝ M (μ i) ∪ μ '' uIcc i sP := by
    simp only [ρ, Path.trans_range, Path.range_segment, Path.range_subpath]
  let base : Path (σ p) (σ q) := Path.segment (σ p) (σ q)
  let half : I := ⟨1 / 2, by norm_num⟩
  have hbaseInjective : Function.Injective base := Path.segment_injective_of_ne hD
  have hbaseMid : base half = M := by
    simp [base, half, Path.segment, AffineMap.lineMap_apply_module, M, Complex.real_smul]
    ring
  have hbaseEnd (i : I) (hi : i = 0 ∨ i = 1) : base i = μ i := by
    rcases hi with rfl | rfl <;> simp
  have hhalfRange (i : I) (hi : i = 0 ∨ i = 1) :
      segment ℝ M (μ i) = base '' uIcc half i := by
    rw [← Path.range_subpath]
    have he : (Path.segment M (μ i) : I → ℂ) = base.subpath half i := by
      rw [← hbaseEnd i hi]
      funext t
      change AffineMap.lineMap M (base i) (t : ℝ) =
        base (Icc.convexComb half i t)
      simp [base, half, Path.segment, AffineMap.lineMap_apply_module,
        M, Complex.real_smul, Path.coe_mk']
      ring
    rw [← he, Path.range_segment]
  have hρ0 : range (ρ 0) = base '' Icc 0 half ∪ μ '' Icc 0 sP := by
    rw [hρRange, hhalfRange 0 (Or.inl rfl)]
    rw [uIcc_of_ge (show (0 : I) ≤ half from half.property.1),
      uIcc_of_le (show (0 : I) ≤ sP from sP.property.1)]
  have hρ1 : range (ρ 1) = base '' Icc half 1 ∪ μ '' Icc sP 1 := by
    rw [hρRange, hhalfRange 1 (Or.inr rfl)]
    rw [uIcc_of_le (show half ≤ (1 : I) from half.property.2),
      uIcc_of_ge (show sP ≤ (1 : I) from sP.property.2)]
  have hintervalCover (t : I) : Icc 0 t ∪ Icc t 1 = (univ : Set I) := by
    ext u
    simp only [mem_union, mem_Icc, mem_univ, iff_true]
    rcases le_total u t with hu | hu
    · exact Or.inl ⟨u.property.1, hu⟩
    · exact Or.inr ⟨hu, u.property.2⟩
  have hρCover : range (ρ 0) ∪ range (ρ 1) = range σ₀ := by
    rw [hρ0, hρ1, union_union_union_comm, ← image_union, ← image_union,
      hintervalCover, hintervalCover, image_univ, image_univ, hcircleRange]
    rw [Path.range_segment]
    congr 1
    exact range_comp σ α
  have hbaseArcMeet (t u : I) (he : base t = μ u) : t = u ∧ (t = 0 ∨ t = 1) := by
    by_cases ht0 : t = 0
    · subst t
      simp only [Path.source] at he
      have hu : u = 0 := hμInjective (he.symm.trans μ.source.symm)
      exact ⟨hu.symm, Or.inl rfl⟩
    by_cases ht1 : t = 1
    · subst t
      simp only [Path.target] at he
      have hu : u = 1 := hμInjective (he.symm.trans μ.target.symm)
      exact ⟨hu.symm, Or.inr rfl⟩
    have htpos : 0 < (t : ℝ) := by
      apply lt_of_le_of_ne t.property.1
      intro he
      exact ht0 (Subtype.ext he.symm)
    have htlt : (t : ℝ) < 1 := by
      apply lt_of_le_of_ne t.property.2
      intro he
      exact ht1 (Subtype.ext he)
    have hm : base t ∈ openSegment ℝ (σ p) (σ q) :=
      lineMap_mem_openSegment ℝ _ _ ⟨htpos, htlt⟩
    apply False.elim
    apply haSub (hChord hm)
    rw [he]
    exact hμCurve ⟨u, rfl⟩
  have hρMeet : range (ρ 0) ∩ range (ρ 1) = {M, μ sP} := by
    apply Subset.antisymm
    · intro z hz
      rw [hρ0, hρ1] at hz
      rcases hz with ⟨hz0 | hz0, hz1 | hz1⟩
      · obtain ⟨t, ht, rfl⟩ := hz0
        obtain ⟨u, hu, he⟩ := hz1
        have htu := hbaseInjective he
        have htHalf : t = half := le_antisymm ht.2 (htu ▸ hu.1)
        simp [htHalf, hbaseMid]
      · obtain ⟨t, ht, rfl⟩ := hz0
        obtain ⟨u, hu, he⟩ := hz1
        obtain ⟨htu, ht0 | ht1⟩ := hbaseArcMeet t u he.symm
        · have hu0 : u = 0 := htu.symm.trans ht0
          have hp := hu.1
          rw [hu0] at hp
          exact False.elim (not_le_of_gt hs0 hp)
        · have hp := ht.2
          rw [ht1] at hp
          change (1 : ℝ) ≤ 1 / 2 at hp
          norm_num at hp
      · obtain ⟨t, ht, rfl⟩ := hz0
        obtain ⟨u, hu, he⟩ := hz1
        obtain ⟨hut, hu0 | hu1⟩ := hbaseArcMeet u t he
        · have hp := hu.1
          rw [hu0] at hp
          change (1 / 2 : ℝ) ≤ 0 at hp
          norm_num at hp
        · have ht1 : t = 1 := hut.symm.trans hu1
          have hp := ht.2
          rw [ht1] at hp
          exact False.elim (not_le_of_gt hs1 hp)
      · obtain ⟨t, ht, rfl⟩ := hz0
        obtain ⟨u, hu, he⟩ := hz1
        have htu := hμInjective he
        have hts : t = sP := le_antisymm ht.2 (htu ▸ hu.1)
        simp [hts]
    · intro z hz
      rcases hz with rfl | hz
      · exact ⟨⟨0, (ρ 0).source⟩, ⟨0, (ρ 1).source⟩⟩
      · have he : z = μ sP := mem_singleton_iff.mp hz
        subst z
        exact ⟨⟨1, (ρ 0).target⟩, ⟨1, (ρ 1).target⟩⟩
  let endpoint : Bool → I := fun i ↦ Bool.rec 0 1 i
  have hendpoint (i : Bool) : endpoint i = 0 ∨ endpoint i = 1 := by
    cases i <;> simp [endpoint]
  have hρSub (i : Bool) : range (ρ (endpoint i)) ⊆ range σ₀ := by
    rw [← hρCover]
    cases i
    · exact subset_union_left
    · exact subset_union_right
  have hσ₀inverse (z : range σ₀) : σ₀ (hσ₀.toHomeomorph.symm z) = z := by
    exact congrArg Subtype.val (hσ₀.toHomeomorph.apply_symm_apply z)
  let αcut (i : Bool) : Path pM pP :=
    { toFun := fun t ↦ hσ₀.toHomeomorph.symm ⟨ρ (endpoint i) t, hρSub i ⟨t, rfl⟩⟩
      continuous_toFun := hσ₀.toHomeomorph.symm.continuous.comp
        ((ρ (endpoint i)).continuous.subtype_mk _)
      source' := by
        apply hσ₀.injective
        exact (hσ₀inverse _).trans ((ρ (endpoint i)).source.trans hpM.symm)
      target' := by
        apply hσ₀.injective
        exact (hσ₀inverse _).trans ((ρ (endpoint i)).target.trans hpP.symm) }
  have hαcutEval (i : Bool) (t : I) : σ₀ (αcut i t) = ρ (endpoint i) t :=
    hσ₀inverse _
  have hαcut (i : Bool) : Topology.IsEmbedding (αcut i) := by
    refine ((αcut i).continuous.isClosedEmbedding ?_).isEmbedding
    intro x y he
    apply hρInjective (endpoint i) (hendpoint i)
    simpa only [hαcutEval] using congrArg σ₀ he
  have hαcutImage (i : Bool) : σ₀ '' range (αcut i) = range (ρ (endpoint i)) := by
    rw [← range_comp]
    congr 1
    funext t
    exact hαcutEval i t
  let α₀ : Path pM pP := αcut false
  let α₀' : Path pM pP := αcut true
  have hα₀ : Topology.IsEmbedding α₀ := hαcut false
  have hα₀' : Topology.IsEmbedding α₀' := hαcut true
  have hnewCover : range α₀ ∪ range α₀' = univ := by
    apply (Set.image_injective.mpr hσ₀.injective)
    rw [image_union, hαcutImage false, hαcutImage true, image_univ]
    exact hρCover
  have hnewMeet : range α₀ ∩ range α₀' = {pM, pP} := by
    apply (Set.image_injective.mpr hσ₀.injective)
    rw [image_inter hσ₀.injective, hαcutImage false, hαcutImage true]
    simpa only [endpoint, Bool.false_eq_true, ↓reduceIte, image_insert_eq,
      image_singleton, hpM, hpP] using hρMeet
  obtain ⟨B₁, B₂, hB₁ne, hB₂ne, hB₁conn, hB₂conn, hB₁open, hB₂open,
    hBdisj, hBcover, hBcomponents, hB₁front, hB₂front, hBlocal⟩ :=
      HolomorphicAnosov.cairns_chord_sector_separation σ₀ hσ₀ pM pP hpMP
        α₀ α₀' hα₀ hα₀' α₀.source α₀.target α₀'.source α₀'.target
        hnewCover hnewMeet β hβNonempty hβBounded hβNewComponent
        (by simpa only [hpM, hpP] using hMPchord)
  have hMPcomponents : ∀ z ∈ β \ openSegment ℝ M (μ sP),
      connectedComponentIn (β \ openSegment ℝ M (μ sP)) z = B₁ ∨
        connectedComponentIn (β \ openSegment ℝ M (μ sP)) z = B₂ := by
    simpa only [hpM, hpP] using hBcomponents
  have hB₁label : frontier B₁ ⊆ range (μ.subpath 0 sP) ∪
      segment ℝ M (σ p) ∪ segment ℝ M (μ sP) := by
    have hi : σ₀ '' range α₀ = segment ℝ M (σ p) ∪ range (μ.subpath 0 sP) := by
      rw [hαcutImage false, hρRange, Path.range_subpath]
      simp [endpoint]
    rw [hi, hpM, hpP] at hB₁front
    intro z hz
    rcases hB₁front hz with hz | hz | hz
    · exact Or.inr hz
    · exact Or.inl (Or.inr hz)
    · exact Or.inl (Or.inl hz)
  have hB₂label : frontier B₂ ⊆ range (μ.subpath 1 sP) ∪
      segment ℝ M (σ q) ∪ segment ℝ M (μ sP) := by
    have hi : σ₀ '' range α₀' = segment ℝ M (σ q) ∪ range (μ.subpath 1 sP) := by
      rw [hαcutImage true, hρRange, Path.range_subpath]
      simp [endpoint]
    rw [hi, hpM, hpP] at hB₂front
    intro z hz
    rcases hB₂front hz with hz | hz | hz
    · exact Or.inr hz
    · exact Or.inl (Or.inr hz)
    · exact Or.inl (Or.inl hz)
  let βhalf : Bool → Set ℂ := fun i ↦ if i then B₂ else B₁
  have hHalfComponent : ∀ i, ∃ z ∈ β \ openSegment ℝ M (μ sP),
      βhalf i = connectedComponentIn (β \ openSegment ℝ M (μ sP)) z := by
    have hc : β \ openSegment ℝ M (μ sP) = B₁ ∪ B₂ := by
      simpa only [hpM, hpP] using hBcover
    intro i
    cases i
    · obtain ⟨z, hz⟩ := hB₁ne
      have hzU : z ∈ β \ openSegment ℝ M (μ sP) := hc.symm ▸ Or.inl hz
      refine ⟨z, hzU, ?_⟩
      rcases hMPcomponents z hzU with he | he
      · exact he.symm
      · have hz₂ : z ∈ B₂ := he ▸ mem_connectedComponentIn hzU
        exact False.elim (Set.disjoint_left.mp hBdisj hz hz₂)
    · obtain ⟨z, hz⟩ := hB₂ne
      have hzU : z ∈ β \ openSegment ℝ M (μ sP) := hc.symm ▸ Or.inr hz
      refine ⟨z, hzU, ?_⟩
      rcases hMPcomponents z hzU with he | he
      · have hz₁ : z ∈ B₁ := he ▸ mem_connectedComponentIn hzU
        exact False.elim (Set.disjoint_left.mp hBdisj hz₁ hz)
      · exact he.symm
  have hHalfFrontier (i : Bool) : frontier (βhalf i) ⊆
      range (μ.subpath (endpoint i) sP) ∪ segment ℝ M (μ (endpoint i)) ∪
        segment ℝ M (μ sP) := by
    cases i
    · change frontier B₁ ⊆ range (μ.subpath 0 sP) ∪
        segment ℝ M (μ 0) ∪ segment ℝ M (μ sP)
      simpa only [Path.source] using hB₁label
    · change frontier B₂ ⊆ range (μ.subpath 1 sP) ∪
        segment ℝ M (μ 1) ∪ segment ℝ M (μ sP)
      simpa only [Path.target] using hB₂label
  have hRayEnters : ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      ∀ t ∈ Ioo (0 : ℝ) η, M + t • (μ sP - M) ∈ β := by
    refine ⟨1, zero_lt_one, le_rfl, ?_⟩
    intro t ht
    apply hMPchord
    convert lineMap_mem_openSegment ℝ M (μ sP) ht using 1
    rw [AffineMap.lineMap_apply_module]
    module
  let W : ℂ := σ q - σ p
  let coord : ℂ → ℂ := fun z ↦ star W * (z - M)
  have hW : W ≠ 0 := sub_ne_zero.mpr hD.symm
  have hnW : 0 < Complex.normSq W := Complex.normSq_pos.mpr hW
  have hcoordOpen : IsOpenMap coord :=
    (Homeomorph.mulLeft₀ (star W) (star_ne_zero.mpr hW)).isOpenMap.comp
      (isOpenMap_sub_right M)
  have hcoordAffine (x y : ℂ) (a b : ℝ) (hab : a + b = 1) :
      coord (a • x + b • y) = a • coord x + b • coord y := by
    have habc : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    change star W * ((a : ℂ) * x + (b : ℂ) * y - M) =
      (a : ℂ) * (star W * (x - M)) + (b : ℂ) * (star W * (y - M))
    calc
      _ = (a : ℂ) * (star W * (x - M)) + (b : ℂ) * (star W * (y - M)) +
          ((a : ℂ) + (b : ℂ) - 1) * star W * M := by ring
      _ = _ := by rw [habc]; ring
  have hcoordM : coord M = 0 := by simp [coord]
  have hcoordD₁ : coord (σ p) = -(Complex.normSq W : ℂ) / 2 := by
    apply Complex.ext <;> simp [coord, W, M, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im] <;> ring
  have hcoordD₂ : coord (σ q) = (Complex.normSq W : ℂ) / 2 := by
    apply Complex.ext <;> simp [coord, W, M, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im] <;> ring
  have hcoordP : coord (μ sP) = (τ * ε * Complex.normSq W : ℝ) * Complex.I := by
    rw [hμContact]
    apply Complex.ext <;> simp [coord, ray, V, W, Complex.real_smul,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring
  let sign : Bool → ℝ := fun i ↦ if i then 1 else -1
  have hsign (i : Bool) : sign i ≠ 0 := by cases i <;> simp [sign]
  have hεne : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hStrictHull (f : ℂ → ℝ) (hf : IsOpenMap f)
      (haff : ∀ x y : ℂ, ∀ a b : ℝ, a + b = 1 →
        f (a • x + b • y) = a * f x + b * f y)
      (i : Bool) (hvertices : ∀ z ∈ ({M, μ sP, μ (endpoint i)} : Set ℂ), 0 ≤ f z) :
      ∀ z ∈ interior (convexHull ℝ {M, μ sP, μ (endpoint i)}), 0 < f z := by
    intro z hz
    exact HolomorphicAnosov.open_affine_positive_on_convexHull_interior f hf haff hvertices hz
  have hTriangleStrict (i : Bool) (z : ℂ)
      (hz : z ∈ interior (convexHull ℝ {M, μ sP, μ (endpoint i)})) :
      0 < ε * (coord z).im ∧ 0 < sign i * (coord z).re := by
    constructor
    · apply hStrictHull (fun z ↦ ε * (coord z).im)
        ((Homeomorph.mulLeft₀ ε hεne).isOpenMap.comp
          (Complex.isOpenMap_im.comp hcoordOpen)) ?_ i ?_ z hz
      · intro x y a b hab
        rw [hcoordAffine x y a b hab]
        simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
        ring
      · intro z hz
        rcases hz with rfl | rfl | hz
        · simp [hcoordM]
        · rw [hcoordP]
          simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
            Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
          rcases hε with rfl | rfl <;> nlinarith [mul_pos hτ hnW]
        · rw [mem_singleton_iff.mp hz]
          cases i <;> simp [endpoint, hcoordD₁, hcoordD₂]
    · apply hStrictHull (fun z ↦ sign i * (coord z).re)
        ((Homeomorph.mulLeft₀ (sign i) (hsign i)).isOpenMap.comp
          (Complex.isOpenMap_re.comp hcoordOpen)) ?_ i ?_ z hz
      · intro x y a b hab
        rw [hcoordAffine x y a b hab]
        simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
        ring
      · intro z hz
        rcases hz with rfl | rfl | hz
        · simp [hcoordM]
        · simp [hcoordP]
        · rw [mem_singleton_iff.mp hz]
          cases i <;> simp [endpoint, hcoordD₁, hcoordD₂, sign] <;> nlinarith [hnW]
  have hcoordCross (z : ℂ) :
      (star (σ q - σ p) * (z - σ p)).im = (coord z).im := by
    simp [coord, W, M, Complex.mul_im]
    ring
  have hMPcoord (z : ℂ) (hz : z ∈ segment ℝ M (μ sP)) : (coord z).re = 0 := by
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    rw [hcoordAffine _ _ _ _ hab, hcoordM, hcoordP]
    simp
  have hNearCut (i : Bool) :
      Metric.ball M r ∩ interior (convexHull ℝ {M, μ sP, μ (endpoint i)}) ⊆
        β \ openSegment ℝ M (μ sP) := by
    intro z hz
    have hs := hTriangleStrict i z hz.2
    refine ⟨hside ⟨hz.1, by rw [hcoordCross]; exact hs.1⟩, ?_⟩
    intro hm
    have hc := hMPcoord z (openSegment_subset_segment ℝ _ _ hm)
    rw [hc, mul_zero] at hs
    exact lt_irrefl 0 hs.2
  have hHalfOpen (i : Bool) : IsOpen (βhalf i) := by
    cases i
    · exact hB₁open
    · exact hB₂open
  have hHalfSub (i : Bool) : βhalf i ⊆ β := by
    obtain ⟨z, hz, he⟩ := hHalfComponent i
    rw [he]
    exact (connectedComponentIn_subset _ _).trans sdiff_subset
  have hHalfCover (i : Bool) : β \ openSegment ℝ M (μ sP) = βhalf i ∪ βhalf (!i) := by
    have hc : β \ openSegment ℝ M (μ sP) = B₁ ∪ B₂ := by
      simpa only [hpM, hpP] using hBcover
    cases i <;> simpa [βhalf, union_comm] using hc
  have hHalfDisjoint (i : Bool) : Disjoint (βhalf i) (βhalf (!i)) := by
    cases i
    · exact hBdisj
    · exact hBdisj.symm
  have hHalfNear : ∀ i, ∃ η : ℝ, 0 < η ∧
      Metric.ball M η ∩ interior (convexHull ℝ {M, μ sP, μ (endpoint i)}) ⊆ βhalf i := by
    clear * - M μ sP endpoint r hr βhalf hHalfCover hNearCut hHalfOpen hHalfDisjoint hball hhalfInterior hβSub hHalfSub hHalfFrontier hμCurve coord sign hcoordAffine hcoordM hcoordD₁ hcoordD₂ hnW hMPcoord σ p q hendpoint haSub
    intro i
    refine ⟨r, hr, ?_⟩
    let K : Set ℂ := convexHull ℝ {M, μ sP, μ (endpoint i)}
    let Q : Set ℂ := Metric.ball M r ∩ interior K
    have hQconvex : Convex ℝ Q := (convex_ball M r).inter (convex_convexHull ℝ _).interior
    have hQsub : Q ⊆ βhalf i ∪ βhalf (!i) := (hHalfCover i) ▸ hNearCut i
    intro z hz
    by_contra hzi
    have hzother : z ∈ βhalf (!i) := (hQsub hz).resolve_left hzi
    have hQother : Q ⊆ βhalf (!i) := hQconvex.isPreconnected.subset_right_of_subset_union
      (hHalfOpen i) (hHalfOpen (!i)) (hHalfDisjoint i) hQsub ⟨z, hz, hzother⟩
    have hc : Continuous (fun t : ℝ ↦ (1 - t) • M + t • μ (endpoint i)) := by fun_prop
    obtain ⟨d, hd, hdist⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := 0)) r hr
    let t : ℝ := min (d / 2) (1 / 2)
    have ht : 0 < t := lt_min (by positivity) (by norm_num)
    have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have htd : t < d := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    let b : ℂ := (1 - t) • M + t • μ (endpoint i)
    have hbball : b ∈ Metric.ball M r := by
      simpa only [b, Metric.mem_ball, sub_zero, one_smul, zero_smul, add_zero] using
        hdist (by simpa [Real.dist_eq, abs_of_pos ht] using htd)
    have hbK : b ∈ K := by
      apply (convex_convexHull ℝ _)
        (subset_convexHull ℝ _ (by simp : M ∈ ({M, μ sP, μ (endpoint i)} : Set ℂ)))
        (subset_convexHull ℝ _ (by simp : μ (endpoint i) ∈ ({M, μ sP, μ (endpoint i)} : Set ℂ)))
        (by linarith only [ht1] : 0 ≤ 1 - t) ht.le
      ring
    have hbclosure : b ∈ closure Q := by
      apply closure_mono (show openSegment ℝ b z ⊆ Q from ?_)
        (segment_subset_closure_openSegment (left_mem_segment ℝ b z))
      intro w hw
      exact ⟨(convex_ball M r).segment_subset hbball hz.1
        (openSegment_subset_segment ℝ b z hw),
        (convex_convexHull ℝ _).openSegment_self_interior_subset_interior hbK hz.2 hw⟩
    have hbbase : b ∈ openSegment ℝ (σ p) (σ q) := by
      simpa [b, Path.segment, AffineMap.lineMap_apply_module] using
        hhalfInterior (endpoint i) (hendpoint i) ⟨t, ht.le, ht1.le⟩ ht1
    have hbnotβ : b ∉ β := fun hb ↦ (hβSub hb).2 hbbase
    have hbnotOther : b ∉ βhalf (!i) := fun hb ↦ hbnotβ (hHalfSub (!i) hb)
    have hbfront : b ∈ frontier (βhalf (!i)) := by
      rw [frontier, (hHalfOpen (!i)).interior_eq]
      exact ⟨closure_mono hQother hbclosure, hbnotOther⟩
    have hbre : 0 < sign i * (coord b).re := by
      dsimp only [b]
      rw [hcoordAffine _ _ _ _ (by ring), hcoordM]
      cases i <;> simp [endpoint, hcoordD₁, hcoordD₂, sign] <;>
        nlinarith only [mul_pos ht hnW]
    have hopposite (w : ℂ) (hw : w ∈ segment ℝ M (μ (endpoint (!i)))) :
        sign i * (coord w).re ≤ 0 := by
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
      rw [hcoordAffine _ _ _ _ hab, hcoordM]
      cases i <;> simp [endpoint, hcoordD₁, hcoordD₂, sign] <;>
        nlinarith only [mul_nonneg hb hnW.le]
    rcases hHalfFrontier (!i) hbfront with (hbcurve | hbopposite) | hbMP
    · obtain ⟨u, hu⟩ := hbcurve
      apply haSub (hball hbball)
      rw [← hu]
      exact hμCurve ⟨_, rfl⟩
    · exact (not_le_of_gt hbre) (hopposite b hbopposite)
    · rw [hMPcoord b hbMP, mul_zero] at hbre
      exact lt_irrefl 0 hbre
  -- The parent's full-sector and supplier's half-sector Case I tests agree.
  have hCaseI (i : Bool) :
      interior (convexHull ℝ {M, μ sP, μ (endpoint i)}) ⊆ β ↔
        interior (convexHull ℝ {M, μ sP, μ (endpoint i)}) ⊆ βhalf i := by
    constructor
    · intro hI z hz
      let K : Set ℂ := convexHull ℝ {M, μ sP, μ (endpoint i)}
      have hK : Convex ℝ K := convex_convexHull ℝ _
      have hM : M ∈ K := subset_convexHull ℝ _ (by simp)
      have hMclosure : M ∈ closure (interior K) := by
        apply closure_mono (hK.openSegment_self_interior_subset_interior hM hz)
        exact segment_subset_closure_openSegment (left_mem_segment ℝ M z)
      obtain ⟨η, hη, hnear⟩ := hHalfNear i
      obtain ⟨w, hw, hwd⟩ := Metric.mem_closure_iff.mp hMclosure η hη
      have hwHalf : w ∈ βhalf i := hnear ⟨by simpa [Metric.mem_ball, dist_comm] using hwd, hw⟩
      have hsub : interior K ⊆ βhalf i ∪ βhalf (!i) := by
        rw [← hHalfCover i]
        intro x hx
        refine ⟨hI hx, ?_⟩
        intro hxMP
        have hstrict := (hTriangleStrict i x hx).2
        rw [hMPcoord x (openSegment_subset_segment ℝ _ _ hxMP), mul_zero] at hstrict
        exact lt_irrefl 0 hstrict
      exact hK.interior.isPreconnected.subset_left_of_subset_union
        (hHalfOpen i) (hHalfOpen (!i)) (hHalfDisjoint i) hsub ⟨w, hw, hwHalf⟩ hz
    · exact fun hI ↦ hI.trans (hHalfSub i)
  have hCaseIIdentities (i : Bool)
      (hI : interior (convexHull ℝ {M, μ sP, μ (endpoint i)}) ⊆ βhalf i) :
      halfFront M (μ sP) (μ (endpoint i))
          (range (μ.subpath (endpoint i) sP)) β = segment ℝ (μ (endpoint i)) (μ sP) ∧
      halfStar M (μ sP) (μ (endpoint i))
          (range (μ.subpath (endpoint i) sP)) β =
        interior (convexHull ℝ {M, μ sP, μ (endpoint i)}) := by
    have hIβ := (hCaseI i).mpr hI
    dsimp only [halfFront, halfStar, triangle]
    constructor
    · exact ite_eq_left hIβ
    · exact ite_eq_left hIβ
  have hCaseIIProvider := HolomorphicAnosov.cairns_half_sector_caseII_identifications
    σ hσ a (by
      obtain ⟨x, hx, he⟩ := haComponent
      exact ⟨x, haSub hx, he.symm⟩) haBounded (σ p) (σ q) hD μ
    hμInjective hμCurve hChord β (by
      obtain ⟨x, hx, he⟩ := hβ
      exact ⟨x, hx, he.symm⟩)
    (by
      change frontier β ⊆ segment ℝ (σ p) (σ q) ∪ range (σ ∘ α)
      rw [range_comp]
      exact hFrontier)
    sP ⟨hs0, hs1⟩ βhalf hperpendicular hfirstContact hRayEnters hHalfComponent
    (by
      intro i
      cases i
      · simpa [endpoint, M] using hHalfFrontier false
      · simpa [endpoint, M] using hHalfFrontier true)
    (by
      intro i
      cases i
      · simpa [endpoint, M] using hHalfNear false
      · simpa [endpoint, M] using hHalfNear true)
  have hCaseIIIdentities (i : Bool)
      (hII : ¬ interior (triangle M (μ sP) (μ (endpoint i))) ⊆ βhalf i) :
      halfFront M (μ sP) (μ (endpoint i)) (range (μ.subpath (endpoint i) sP)) β =
        {Q | Q ∈ halfHull M (μ sP) (μ (endpoint i)) (range (μ.subpath (endpoint i) sP)) ∧
          IsVisible ℝ (halfHull M (μ sP) (μ (endpoint i))
            (range (μ.subpath (endpoint i) sP))) M Q} ∧
      halfStar M (μ sP) (μ (endpoint i)) (range (μ.subpath (endpoint i) sP)) β =
        {x | x ∈ interior (triangle M (μ sP) (μ (endpoint i))) \
            halfHull M (μ sP) (μ (endpoint i)) (range (μ.subpath (endpoint i) sP)) ∧
          M ∈ closure (connectedComponentIn
            (interior (triangle M (μ sP) (μ (endpoint i))) \
              halfHull M (μ sP) (μ (endpoint i)) (range (μ.subpath (endpoint i) sP))) x)} := by
    have hIIβ := mt (hCaseI i).mp hII
    cases i
    · have hraw := hCaseIIProvider false (by simpa [triangle, endpoint, M] using hII)
      simp [endpoint, M] at hIIβ
      simpa only [halfFront, halfStar, halfHull, triangle, endpoint, M, hIIβ, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using hraw
    · have hraw := hCaseIIProvider true (by simpa [triangle, endpoint, M] using hII)
      simp [endpoint, M] at hIIβ
      simpa only [halfFront, halfStar, halfHull, triangle, endpoint, M, hIIβ, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using hraw
  have hHalfGeometry := HolomorphicAnosov.halfSectorConvexFront
    σ hσ a (by
      obtain ⟨x, hx, he⟩ := haComponent
      exact ⟨x, haSub hx, he.symm⟩) haBounded (σ p) (σ q) hD μ
    hμInjective hμCurve hChord β (by
      obtain ⟨x, hx, he⟩ := hβ
      exact ⟨x, hx, he.symm⟩)
    (by
      change frontier β ⊆ segment ℝ (σ p) (σ q) ∪ range (σ ∘ α)
      rw [range_comp]
      exact hFrontier)
    sP ⟨hs0, hs1⟩ βhalf hperpendicular hfirstContact hRayEnters hHalfComponent
    (by
      intro i
      cases i
      · simpa [endpoint, M] using hHalfFrontier false
      · simpa [endpoint, M] using hHalfFrontier true)
    (by
      intro i
      cases i
      · simpa [endpoint, M] using hHalfNear false
      · simpa [endpoint, M] using hHalfNear true)
  have hLiteralFront (i : Bool) :
      halfFront M (μ sP) (μ (endpoint i)) (range (μ.subpath (endpoint i) sP)) β =
        if interior (triangle M (μ sP) (μ (endpoint i))) ⊆ βhalf i
        then segment ℝ (μ (endpoint i)) (μ sP)
        else {Q | Q ∈ halfHull M (μ sP) (μ (endpoint i)) (range (μ.subpath (endpoint i) sP)) ∧
          IsVisible ℝ (halfHull M (μ sP) (μ (endpoint i))
            (range (μ.subpath (endpoint i) sP))) M Q} := by
    by_cases hI : interior (triangle M (μ sP) (μ (endpoint i))) ⊆ βhalf i
    · rw [ite_eq_left hI]
      exact (hCaseIIdentities i hI).1
    · rw [ite_eq_right hI]
      exact (hCaseIIIdentities i hI).1
  have hLiteralStar (i : Bool) :
      halfStar M (μ sP) (μ (endpoint i)) (range (μ.subpath (endpoint i) sP)) β =
        if interior (triangle M (μ sP) (μ (endpoint i))) ⊆ βhalf i
        then interior (triangle M (μ sP) (μ (endpoint i)))
        else {x | x ∈ interior (triangle M (μ sP) (μ (endpoint i))) \
            halfHull M (μ sP) (μ (endpoint i)) (range (μ.subpath (endpoint i) sP)) ∧
          M ∈ closure (connectedComponentIn
            (interior (triangle M (μ sP) (μ (endpoint i))) \
              halfHull M (μ sP) (μ (endpoint i)) (range (μ.subpath (endpoint i) sP))) x)} := by
    by_cases hI : interior (triangle M (μ sP) (μ (endpoint i))) ⊆ βhalf i
    · rw [ite_eq_left hI]
      exact (hCaseIIdentities i hI).2
    · rw [ite_eq_right hI]
      exact (hCaseIIIdentities i hI).2
  have hLiteralHalfGeometry (i : Bool) :
      IsCompact (halfFront M (μ sP) (μ (endpoint i)) (range (μ.subpath (endpoint i) sP)) β) ∧
      (halfStar M (μ sP) (μ (endpoint i)) (range (μ.subpath (endpoint i) sP)) β).Nonempty ∧
      IsOpen (halfStar M (μ sP) (μ (endpoint i)) (range (μ.subpath (endpoint i) sP)) β) ∧
      halfStar M (μ sP) (μ (endpoint i)) (range (μ.subpath (endpoint i) sP)) β ⊆ βhalf i := by
    rw [hLiteralFront i, hLiteralStar i]
    cases i
    · simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using hHalfGeometry.1 false
    · simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using hHalfGeometry.1 true
  obtain ⟨_, _, hHalfParam, _, hHalfNorm, hHalfSegments, _, _, hHalfContact, hHalfGaps, hOpenSource, hConnectedSource,
    hSourceSubset, hSourceFrontier, hSourceClosure, hSourceUnique⟩ := hHalfGeometry
  obtain ⟨LF, hLFFold⟩ : ∃ LF : Bool → Set ℂ,
      LF = fun i ↦ halfFront M (μ sP) (μ (endpoint i))
        (range (μ.subpath (endpoint i) sP)) β := ⟨_, rfl⟩
  obtain ⟨BS, hBSFold⟩ : ∃ BS : Bool → Set ℂ,
      BS = fun i ↦ halfStar M (μ sP) (μ (endpoint i))
        (range (μ.subpath (endpoint i) sP)) β := ⟨_, rfl⟩
  have hLiteralHalfGeometry (i : Bool) :
      IsCompact (LF i) ∧ (BS i).Nonempty ∧ IsOpen (BS i) ∧ BS i ⊆ βhalf i := by
    simpa only [hLFFold, hBSFold] using hLiteralHalfGeometry i
  have hSourceOpen : IsOpen (BS false ∪ BS true ∪ openSegment ℝ M (μ sP)) := by
    simp only [hBSFold]
    rw [hLiteralStar false, hLiteralStar true]
    simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using hOpenSource
  have hSourceSub : BS false ∪ BS true ∪ openSegment ℝ M (μ sP) ⊆ β := by
    simp only [hBSFold]
    rw [hLiteralStar false, hLiteralStar true]
    simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using hSourceSubset
  have hSourceFront : frontier (BS false ∪ BS true ∪ openSegment ℝ M (μ sP)) =
      segment ℝ (σ p) (σ q) ∪ (LF false ∪ LF true) := by
    simp only [hBSFold, hLFFold]
    rw [hLiteralStar false, hLiteralStar true, hLiteralFront false, hLiteralFront true]
    simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using hSourceFrontier
  have hLiteralSweep : closure (BS false ∪ BS true ∪ openSegment ℝ M (μ sP)) =
      sweep M (LF false ∪ LF true) := by
    have hClosedSegments : closure (BS false ∪ BS true ∪ openSegment ℝ M (μ sP)) =
        ⋃ Q ∈ LF false ∪ LF true, segment ℝ M Q := by
      simp only [hBSFold, hLFFold]
      rw [hLiteralStar false, hLiteralStar true, hLiteralFront false, hLiteralFront true]
      simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using hSourceClosure
    rw [hClosedSegments]
    ext z
    simp only [mem_iUnion, segment_eq_image, mem_image, sweep, mem_ofPred_eq]
    constructor
    · rintro ⟨Q, hQ, t, ht, hz⟩
      exact ⟨Q, hQ, t, ht, hz.symm⟩
    · rintro ⟨Q, hQ, t, ht, hz⟩
      exact ⟨Q, hQ, t, ht, hz.symm⟩
  have hLiteralUnique : ∀ x ∈ closure (BS false ∪ BS true ∪ openSegment ℝ M (μ sP)),
      x ≠ M → ∃! z : ↥(LF false ∪ LF true) × ℝ,
        0 < z.2 ∧ z.2 ≤ 1 ∧ x = (1 - z.2) • M + z.2 • (z.1 : ℂ) := by
    intro x hx hxM
    have hx' : _ := hx
    simp only [hBSFold] at hx'
    rw [hLiteralStar false, hLiteralStar true] at hx'
    obtain ⟨⟨Q,t⟩, hQt, huniq⟩ := hSourceUnique x
      (by simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using hx') hxM
    have hQ : (Q : ℂ) ∈ LF false ∪ LF true := by
      simp only [hLFFold]
      rw [hLiteralFront false, hLiteralFront true]
      simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using Q.property
    refine ⟨(⟨Q,hQ⟩,t), hQt, ?_⟩
    rintro ⟨⟨R,hR⟩,u⟩ hu
    simp only [hLFFold] at hR
    rw [hLiteralFront false, hLiteralFront true] at hR
    have heq := huniq (⟨⟨(R : ℂ), by
      simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using hR⟩,u⟩) hu
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun w ↦ (w.1 : ℂ)) heq)
    · change u = t
      exact congrArg Prod.snd heq
  have hLiteralUniqueI : ∀ x ∈ closure (BS false ∪ BS true ∪ openSegment ℝ M (μ sP)),
      x ≠ M → ∃! w : ↥(LF false ∪ LF true) × I,
        x = (1 - (w.2 : ℝ)) • M + (w.2 : ℝ) • (w.1 : ℂ) := by
    intro x hx hxM
    obtain ⟨⟨Q,t⟩, ⟨ht0, ht1, hxt⟩, huniq⟩ := hLiteralUnique x hx hxM
    refine ⟨(Q, ⟨t, ht0.le, ht1⟩), hxt, ?_⟩
    rintro ⟨R,u⟩ hu
    have hu0 : 0 < (u : ℝ) := by
      apply lt_of_le_of_ne u.property.1
      intro he
      apply hxM
      simpa [← he] using hu
    have heq := huniq (R, (u : ℝ)) ⟨hu0, u.property.2, hu⟩
    apply Prod.ext
    · change R = Q
      exact congrArg Prod.fst heq
    · apply Subtype.ext
      exact congrArg Prod.snd heq
  have hSourceStrictSide : ∀ z ∈ BS false ∪ BS true ∪ openSegment ℝ M (μ sP),
      0 < (star (σ q - σ p) * (μ sP - σ p)).im *
        (star (σ q - σ p) * (z - σ p)).im := by
    intro z hz
    have him : 0 < ε * (coord z).im := by
      rcases hz with (hz | hz) | hz
      · apply (hTriangleStrict false z ?_).1
        simp only [hBSFold] at hz
        change z ∈ halfStar M (μ sP) (μ (endpoint false))
          (range (μ.subpath (endpoint false) sP)) β at hz
        unfold halfStar at hz
        split_ifs at hz
        · exact hz
        · exact hz.1
      · apply (hTriangleStrict true z ?_).1
        simp only [hBSFold] at hz
        change z ∈ halfStar M (μ sP) (μ (endpoint true))
          (range (μ.subpath (endpoint true) sP)) β at hz
        unfold halfStar at hz
        split_ifs at hz
        · exact hz
        · exact hz.1
      · obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
        rw [hcoordAffine _ _ _ _ hab, hcoordM, hcoordP]
        simp only [smul_zero, zero_add, Complex.smul_im, smul_eq_mul,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im, mul_one, mul_zero, zero_add, add_zero]
        rcases hε with rfl | rfl <;> nlinarith [mul_pos hb (mul_pos hτ hnW)]
    rw [hcoordCross, hcoordCross, hcoordP]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
    convert mul_pos (mul_pos hτ hnW) him using 1; ring
  have hLiteralOpenStar : BS false ∪ BS true ∪ openSegment ℝ M (μ sP) =
      openStar (σ p) (σ q) (μ sP) M (LF false ∪ LF true) := by
    let S := BS false ∪ BS true ∪ openSegment ℝ M (μ sP)
    have hNotFront : ∀ x ∈ S, x ∉ frontier S := by
      intro x hx hf
      exact hf.2 (hSourceOpen.interior_eq.symm ▸ hx)
    have hBaseCross : ∀ x ∈ segment ℝ (σ p) (σ q),
        (star (σ q - σ p) * (x - σ p)).im = 0 := by
      rintro x ⟨a, b, ha, hb, hab, rfl⟩
      rw [hcoordCross, hcoordAffine _ _ _ _ hab, hcoordD₁, hcoordD₂]
      simp
    ext x
    constructor
    · intro hx
      have hside := hSourceStrictSide x hx
      have hxM : x ≠ M := by
        intro he
        simp only [he, hcoordCross, hcoordM, Complex.zero_im, mul_zero] at hside
        simp at hside
      obtain ⟨⟨Q,t⟩, ⟨ht0, ht1, hxt⟩, huniq⟩ :=
        hLiteralUnique x (subset_closure hx) hxM
      have htlt : t < 1 := by
        apply lt_of_le_of_ne ht1
        intro ht
        have htR : t = 1 := ht
        have hxt' := hxt
        rw [htR] at hxt'
        have hxQ : x = (Q : ℂ) := by simpa using hxt'
        apply hNotFront x hx
        rw [hSourceFront]
        exact Or.inr (hxQ.symm ▸ Q.property)
      exact ⟨Q, Q.property, t, ⟨ht0, htlt⟩, hxt, hside⟩
    · rintro ⟨Q, hQ, t, ht, hxt, hside⟩
      have hxcl : x ∈ closure S := by
        rw [hLiteralSweep]
        exact ⟨Q, hQ, t, ⟨ht.1.le, ht.2.le⟩, hxt⟩
      by_contra hx
      have hfront : x ∈ frontier S := ⟨hxcl, fun hi ↦ hx (interior_subset hi)⟩
      rw [hSourceFront] at hfront
      rcases hfront with hbase | hxL
      · rw [hBaseCross x hbase] at hside
        simp at hside
      · have hxM : x ≠ M := by
          intro he
          simp only [he, hcoordCross, hcoordM, Complex.zero_im, mul_zero] at hside
          simp at hside
        have heq : ((⟨Q,hQ⟩ : ↥(LF false ∪ LF true)),t) =
            ((⟨x,hxL⟩ : ↥(LF false ∪ LF true)),(1 : ℝ)) :=
          (hLiteralUnique x hxcl hxM).unique
            ⟨ht.1, ht.2.le, hxt⟩ ⟨by norm_num, le_rfl, by simp⟩
        exact ht.2.ne (congrArg Prod.snd heq)
  have hSourceCompact : IsCompact (LF false ∪ LF true) :=
    (hLiteralHalfGeometry false).1.union (hLiteralHalfGeometry true).1
  have hSourceContactClosed : IsClosed ((LF false ∪ LF true) ∩ range σ) :=
    hSourceCompact.isClosed.inter hcCompact.isClosed
  have hSourceContactSub : (LF false ∪ LF true) ∩ range σ ⊆ range μ := by
    clear * - LF σ μ endpoint sP hLFFold hLiteralFront hHalfContact M
    rintro z ⟨hz, hzc⟩
    have hsub (i : Bool) (hzi : z ∈ LF i) : z ∈ range (μ.subpath (endpoint i) sP) := by
      have hzi' := hzi
      simp only [hLFFold] at hzi'
      rw [hLiteralFront i] at hzi'
      cases i
      · have hraw := (hHalfContact false).1
        have hzraw : _ := And.intro hzi' hzc
        have hmem := hraw (by simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target, mem_inter_iff] using hzraw)
        simpa [endpoint] using hmem
      · have hraw := (hHalfContact true).1
        have hzraw : _ := And.intro hzi' hzc
        have hmem := hraw (by simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target, mem_inter_iff] using hzraw)
        simpa [endpoint] using hmem
    rcases hz with hz | hz
    · have hz' := hsub false hz
      rw [Path.range_subpath] at hz'
      exact image_subset_range _ _ hz'
    · have hz' := hsub true hz
      rw [Path.range_subpath] at hz'
      exact image_subset_range _ _ hz'
  have hLiteralHalfGapCover (i : Bool) (x : ℂ) (hx : x ∈ LF i \ range σ) :
      ∃ y z : ℂ, y ≠ z ∧ y ∈ LF i ∩ range σ ∧ z ∈ LF i ∩ range σ ∧
        x ∈ openSegment ℝ y z ∧ openSegment ℝ y z ⊆ LF i \ range σ ∧
        openSegment ℝ y z ⊆ βhalf i := by
    let m : I → ℂ := μ.subpath (endpoint i) sP
    let gaps : Set (I × I) := {g | g.1 < g.2 ∧ m g.1 ∈ LF i ∩ range σ ∧
      m g.2 ∈ LF i ∩ range σ ∧ Disjoint (m '' Ioo g.1 g.2) (LF i ∩ range σ)}
    have hgapData :
        (LF i \ range σ = ⋃ g ∈ gaps, openSegment ℝ (m g.1) (m g.2)) ∧
        ∀ g ∈ gaps, m g.1 ≠ m g.2 ∧ openSegment ℝ (m g.1) (m g.2) ⊆ βhalf i := by
      have hg := hHalfGaps i
      have hp := fun (g : I × I) (hg' : _) ↦
        And.intro (hg.2.2.2 g hg').1 (hg.2.2.2 g hg').2.1
      have hd := And.intro hg.2.1 hp
      dsimp only [gaps, m]
      simp only [hLFFold]
      rw [hLiteralFront i]
      cases i
      · simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using
          hd
      · simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using
          hd
    obtain ⟨g, hxg⟩ := mem_iUnion.mp (hgapData.1 ▸ hx)
    obtain ⟨hg, hxg⟩ := mem_iUnion.mp hxg
    refine ⟨m g.1, m g.2, (hgapData.2 g hg).1, hg.2.1, hg.2.2.1, hxg, ?_,
      (hgapData.2 g hg).2⟩
    rw [hgapData.1]
    exact subset_iUnion₂_of_subset g hg (subset_refl _)
  have hSourceSegmentCover (x : ℂ) (hx : x ∈ (LF false ∪ LF true) \ range σ) :
      ∃ y z : ℂ, y ≠ z ∧ y ∈ (LF false ∪ LF true) ∩ range σ ∧
        z ∈ (LF false ∪ LF true) ∩ range σ ∧ x ∈ openSegment ℝ y z ∧
        openSegment ℝ y z ⊆ (LF false ∪ LF true) \ range σ ∧
        openSegment ℝ y z ⊆ a := by
    have hhalf (i : Bool) (hxi : x ∈ LF i) := hLiteralHalfGapCover i x ⟨hxi, hx.2⟩
    rcases hx.1 with hxL | hxR
    · obtain ⟨y, z, hyz, hy, hz, hxg, hsub, hβg⟩ := hhalf false hxL
      exact ⟨y, z, hyz, ⟨Or.inl hy.1, hy.2⟩, ⟨Or.inl hz.1, hz.2⟩, hxg,
        fun w hw ↦ ⟨Or.inl (hsub hw).1, (hsub hw).2⟩,
        hβg.trans ((hHalfSub false).trans (hβSub.trans sdiff_subset))⟩
    · obtain ⟨y, z, hyz, hy, hz, hxg, hsub, hβg⟩ := hhalf true hxR
      exact ⟨y, z, hyz, ⟨Or.inr hy.1, hy.2⟩, ⟨Or.inr hz.1, hz.2⟩, hxg,
        fun w hw ↦ ⟨Or.inr (hsub hw).1, (hsub hw).2⟩,
        hβg.trans ((hHalfSub true).trans (hβSub.trans sdiff_subset))⟩
  have hSourceFrontEndpoints (i : Bool) : μ (endpoint i) ∈ LF i ∧ μ sP ∈ LF i := by
    obtain ⟨param, hparam, _⟩ := hHalfParam
    have hD := (param i 0).property
    have hP' := (param i 1).property
    rw [(hparam i).1] at hD
    rw [(hparam i).2] at hP'
    simp only [hLFFold]
    rw [hLiteralFront i]
    cases i
    · simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using And.intro hD hP'
    · simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using And.intro hD hP'
  have hFrontStrict (i : Bool) (Q : ℂ) (hQ : Q ∈ LF i)
      (hQD : Q ≠ μ (endpoint i)) (hQP : Q ≠ μ sP) :
      0 < sign i * (coord Q).re := by
    clear * - i Q hQ hQD hQP sign coord M μ sP LF BS endpoint hLFFold hBSFold hLiteralFront hLiteralStar hHalfSegments hTriangleStrict hcoordAffine hcoordM
    have hsegments : openSegment ℝ M Q ⊆ BS i := by
      simp only [hLFFold] at hQ
      rw [hLiteralFront i] at hQ
      simp only [hBSFold]
      rw [hLiteralStar i]
      cases i
      · have hm := hHalfSegments false Q
        simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using
          hm (by simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using hQ)
            (by simpa [endpoint] using hQD) hQP
      · have hm := hHalfSegments true Q
        simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using
          hm (by simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using hQ)
            (by simpa [endpoint] using hQD) hQP
    have hz := hsegments (show (1 / 2 : ℝ) • M + (1 / 2 : ℝ) • Q ∈
        openSegment ℝ M Q from ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, rfl⟩)
    have hztri : (1 / 2 : ℝ) • M + (1 / 2 : ℝ) • Q ∈
        interior (triangle M (μ sP) (μ (endpoint i))) := by
      simp only [hBSFold, halfStar] at hz
      split_ifs at hz
      · exact hz
      · exact hz.1
    have hr := (hTriangleStrict i _ hztri).2
    rw [hcoordAffine _ _ _ _ (by norm_num), hcoordM] at hr
    simp only [smul_zero, zero_add, Complex.smul_re, smul_eq_mul] at hr
    nlinarith
  have hFrontMeet : LF false ∩ LF true = {μ sP} := by
    ext Q
    constructor
    · rintro ⟨hl, hr⟩
      by_contra hQP
      have hQP' : Q ≠ μ sP := hQP
      have hleft : (coord Q).re < 0 := by
        by_cases hQD : Q = μ (endpoint false)
        · rw [hQD]
          have hc : coord (μ (endpoint false)) = -(Complex.normSq W : ℂ) / 2 := by
            simpa [endpoint] using hcoordD₁
          rw [hc]
          simp only [Complex.div_ofNat, Complex.neg_re, Complex.ofReal_re]
          linarith
        · have hh := hFrontStrict false Q hl hQD hQP'
          simpa [sign] using hh
      have hright : 0 < (coord Q).re := by
        by_cases hQD : Q = μ (endpoint true)
        · rw [hQD]
          simpa [endpoint, hcoordD₂] using (half_pos hnW)
        · simpa [sign] using hFrontStrict true Q hr hQD hQP'
      exact (lt_asymm hleft hright)
    · intro hQ
      rw [mem_singleton_iff] at hQ
      subst Q
      exact ⟨(hSourceFrontEndpoints false).2, (hSourceFrontEndpoints true).2⟩
  have hCompactHalfParam :
      ∃ param : ∀ i : Bool, I ≃ₜ LF i,
        (∀ i, (param i 0 : ℂ) = μ (endpoint i) ∧ (param i 1 : ℂ) = μ sP) ∧
        ∀ (i : Bool) (s t p q : I),
          (param i s : ℂ) = μ.subpath (endpoint i) sP p →
          (param i t : ℂ) = μ.subpath (endpoint i) sP q → (s ≤ t ↔ p ≤ q) := by
    obtain ⟨param, hend, horder⟩ := hHalfParam
    let converted (i : Bool) : I ≃ₜ LF i := (param i).trans (Homeomorph.setCongr (by
      simp only [hLFFold]
      rw [hLiteralFront i]
      cases i <;> simp only [triangle, halfHull, endpoint, M, Bool.false_eq_true,
        ↓reduceIte, Path.source, Path.target]))
    refine ⟨converted, ?_, ?_⟩
    · intro i
      change (param i 0 : ℂ) = μ (endpoint i) ∧ (param i 1 : ℂ) = μ sP
      cases i
      · simpa only [endpoint, Path.source, Path.target, Bool.false_eq_true, ↓reduceIte] using hend false
      · simpa only [endpoint, Path.source, Path.target, Bool.false_eq_true, ↓reduceIte] using hend true
    · intro i s t p q hp hq
      change (param i s : ℂ) = μ.subpath (endpoint i) sP p at hp
      change (param i t : ℂ) = μ.subpath (endpoint i) sP q at hq
      cases i <;> exact horder _ s t p q hp hq
  obtain ⟨halfParam, hHalfParamEndpoints, hHalfParamOrder⟩ := hCompactHalfParam
  let frontPath (i : Bool) : Path (μ (endpoint i)) (μ sP) :=
    ⟨⟨fun t ↦ (halfParam i t : ℂ), continuous_subtype_val.comp (halfParam i).continuous⟩,
      (hHalfParamEndpoints i).1, (hHalfParamEndpoints i).2⟩
  have hFrontPathInj (i : Bool) : Function.Injective (frontPath i) := by
    intro u v huv
    exact (halfParam i).injective (Subtype.ext huv)
  have hFrontPathRange (i : Bool) : range (frontPath i) = LF i := by
    ext Q
    constructor
    · rintro ⟨t, rfl⟩
      exact (halfParam i t).property
    · intro hQ
      obtain ⟨t, ht⟩ := (halfParam i).surjective ⟨Q, hQ⟩
      exact ⟨t, congrArg Subtype.val ht⟩
  have hFrontContactLift (i : Bool) (s u : I) (hs : frontPath i s = μ u) :
      ∃ v : I, μ.subpath (endpoint i) sP v = μ u := by
    have hQ := (halfParam i s).property
    have hc : (halfParam i s : ℂ) ∈ range σ := by
      rw [show (halfParam i s : ℂ) = μ u from hs]
      exact hμCurve ⟨u, rfl⟩
    have hm : (halfParam i s : ℂ) ∈ range (μ.subpath (endpoint i) sP) := by
      have hQ := (congrArg (fun S : Set ℂ ↦ (halfParam i s : ℂ) ∈ S)
        (hLiteralFront i)).mp (by simpa only [hLFFold] using hQ)
      cases i
      · exact (hHalfContact false).1 ⟨by
          simpa only [triangle, halfHull, endpoint, M, Path.source, Bool.false_eq_true, ↓reduceIte] using hQ, hc⟩
      · exact (hHalfContact true).1 ⟨by
          simpa only [triangle, halfHull, endpoint, M, Path.target, Bool.false_eq_true, ↓reduceIte] using hQ, hc⟩
    obtain ⟨v, hv⟩ := hm
    exact ⟨v, hv.trans hs⟩
  have hFrontContactOrder (i : Bool) (s t u v : I)
      (hs : frontPath i s = μ u) (ht : frontPath i t = μ v) :
      if i then (u ≤ v ↔ t ≤ s) else (u ≤ v ↔ s ≤ t) := by
    obtain ⟨p', hp'⟩ := hFrontContactLift i s u hs
    obtain ⟨q', hq'⟩ := hFrontContactLift i t v ht
    have hu := congrArg Subtype.val (hμInjective hp')
    have hv := congrArg Subtype.val (hμInjective hq')
    cases i
    · have ho := hHalfParamOrder false s t p' q' (hs.trans hp'.symm) (ht.trans hq'.symm)
      change (1 - (p' : ℝ)) * 0 + p' * sP = (u : ℝ) at hu
      change (1 - (q' : ℝ)) * 0 + q' * sP = (v : ℝ) at hv
      change u ≤ v ↔ s ≤ t
      rw [ho]
      constructor
      · intro huv
        change (p' : ℝ) ≤ q'
        have huv' : (u : ℝ) ≤ v := huv
        nlinarith
      · intro hpq'
        change (u : ℝ) ≤ v
        have hpq'' : (p' : ℝ) ≤ q' := hpq'
        nlinarith
    · have ho := hHalfParamOrder true t s q' p' (ht.trans hq'.symm) (hs.trans hp'.symm)
      change (1 - (p' : ℝ)) * 1 + p' * sP = (u : ℝ) at hu
      change (1 - (q' : ℝ)) * 1 + q' * sP = (v : ℝ) at hv
      change u ≤ v ↔ t ≤ s
      rw [ho]
      constructor
      · intro huv
        change (q' : ℝ) ≤ p'
        have huv' : (u : ℝ) ≤ v := huv
        nlinarith
      · intro hpq'
        change (u : ℝ) ≤ v
        have hpq'' : (q' : ℝ) ≤ p' := hpq'
        nlinarith
  let fullFrontPath := (frontPath false).trans (frontPath true).symm
  have hFullFrontOrder (s t u v : I)
      (hs : fullFrontPath s = μ u) (ht : fullFrontPath t = μ v) : (u ≤ v ↔ s ≤ t) := by
    apply HolomorphicAnosov.path_trans_contact_order μ sP (frontPath false)
      (frontPath true).symm ?_ ?_ s t u v hs ht
    · intro s t u v hs ht
      exact hFrontContactOrder false s t u v hs ht
    · intro s t u v hs ht
      simpa only [Bool.true_eq, ite_true, unitInterval.symm_le_symm] using
        hFrontContactOrder true (unitInterval.symm s) (unitInterval.symm t) u v hs ht
  have hFullFrontEmbedding : Topology.IsEmbedding fullFrontPath :=
    (embedded_path_trans_singleton_inter_exact (frontPath false) (frontPath true).symm
      (hFrontPathInj false) ((hFrontPathInj true).comp unitInterval.symm_bijective.injective)
      (by rw [Path.symm_range, hFrontPathRange, hFrontPathRange, hFrontMeet])).1
  have hFullFrontRange : range fullFrontPath = LF false ∪ LF true := by
    simp only [fullFrontPath, Path.trans_range, Path.symm_range, hFrontPathRange]
  let sourceFrontParam : I ≃ₜ ↥(LF false ∪ LF true) :=
    hFullFrontEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hFullFrontRange)
  have hSourceGapPairs : gapPairs μ ((LF false ∪ LF true) ∩ range σ) =
      gapPairs (fun t : I ↦ (sourceFrontParam t : ℂ)) ((LF false ∪ LF true) ∩ range σ) := by
    apply HolomorphicAnosov.ordered_contact_gap_pairs μ
      (fun t : I ↦ (sourceFrontParam t : ℂ)) _ hμInjective
      (Subtype.val_injective.comp sourceFrontParam.injective) hSourceContactSub
    · rintro Q ⟨hQ, hc⟩
      obtain ⟨t, ht⟩ := sourceFrontParam.surjective ⟨Q,hQ⟩
      exact ⟨t, congrArg Subtype.val ht⟩
    · intro u v s t hu hv hs ht
      exact hFullFrontOrder s t u v hs ht
  have hSourceFrontParamEndpoints : (sourceFrontParam 0 : ℂ) = σ p ∧
      (sourceFrontParam 1 : ℂ) = σ q := by
    change fullFrontPath 0 = σ p ∧ fullFrontPath 1 = σ q
    simp [fullFrontPath, endpoint]
  have hSourceFrontEmbedding : Topology.IsEmbedding (fun t : I ↦ (sourceFrontParam t : ℂ)) :=
    Topology.IsEmbedding.subtypeVal.comp sourceFrontParam.isEmbedding
  have hSourceFrontRange : range (fun t : I ↦ (sourceFrontParam t : ℂ)) = LF false ∪ LF true := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (sourceFrontParam t).property
    · intro hx
      obtain ⟨t, ht⟩ := sourceFrontParam.surjective ⟨x, hx⟩
      exact ⟨t, congrArg Subtype.val ht⟩
  have hSourceGapGeometry (l r : I) (hlr : l < r)
      (hl : (sourceFrontParam l : ℂ) ∈ (LF false ∪ LF true) ∩ range σ)
      (hr : (sourceFrontParam r : ℂ) ∈ (LF false ∪ LF true) ∩ range σ)
      (hgap : ∀ t : I, l < t → t < r →
        (sourceFrontParam t : ℂ) ∉ (LF false ∪ LF true) ∩ range σ) :
      (fun t : I ↦ (sourceFrontParam t : ℂ)) '' Ioo l r =
        openSegment ℝ (sourceFrontParam l : ℂ) (sourceFrontParam r : ℂ) ∧
      openSegment ℝ (sourceFrontParam l : ℂ) (sourceFrontParam r : ℂ) ⊆ a ∧
      Disjoint (openSegment ℝ (sourceFrontParam l : ℂ) (sourceFrontParam r : ℂ)) (range σ) := by
    have himage : (fun t : I ↦ (sourceFrontParam t : ℂ)) '' Ioo l r ⊆
        (LF false ∪ LF true) \ range σ := by
      rintro x ⟨t, ht, rfl⟩
      exact ⟨(sourceFrontParam t).property, fun hc ↦
        hgap t ht.1 ht.2 ⟨(sourceFrontParam t).property, hc⟩⟩
    have heq := HolomorphicAnosov.embedded_interval_gap_segment
      (fun t : I ↦ (sourceFrontParam t : ℂ)) hSourceFrontEmbedding
      ((LF false ∪ LF true) ∩ range σ) l r hlr hl hr hgap (by
        intro x hx
        obtain ⟨y, z, hyz, hy, hz, hxg, hsub, _⟩ := hSourceSegmentCover x (himage hx)
        refine ⟨y, z, hyz, hy, hz, hxg, ?_⟩
        rw [hSourceFrontRange]
        intro w hw
        exact ⟨(hsub hw).1, fun hc ↦ (hsub hw).2 hc.2⟩)
    refine ⟨heq, ?_, ?_⟩
    · rw [← heq]
      intro x hx
      obtain ⟨y, z, _, _, _, hxg, _, ha⟩ := hSourceSegmentCover x (himage hx)
      exact ha hxg
    · apply disjoint_left.mpr
      intro x hx hc
      exact (himage (heq.symm ▸ hx)).2 hc
  have hSourceContactEndpoints : σ p ∈ (LF false ∪ LF true) ∩ range σ ∧
      σ q ∈ (LF false ∪ LF true) ∩ range σ ∧
      μ sP ∈ (LF false ∪ LF true) ∩ range σ := by
    refine ⟨⟨Or.inl ?_, ⟨p, rfl⟩⟩, ⟨Or.inr ?_, ⟨q, rfl⟩⟩,
      ⟨Or.inl (hSourceFrontEndpoints false).2, hμCurve ⟨sP, rfl⟩⟩⟩
    · simpa [endpoint] using (hSourceFrontEndpoints false).1
    · simpa [endpoint] using (hSourceFrontEndpoints true).1
  have hμrange : range μ = σ '' range α := by
    change range (σ ∘ α) = _
    rw [range_comp]
  have hSourceCurveMeet : range σ ∩
      closure (BS false ∪ BS true ∪ openSegment ℝ M (μ sP)) =
      (LF false ∪ LF true) ∩ range σ := by
    ext z
    constructor
    · rintro ⟨hzc, hzcl⟩
      have hzNot : z ∉ BS false ∪ BS true ∪ openSegment ℝ M (μ sP) := by
        intro hz
        exact haSub (hβSub (hSourceSub hz)).1 hzc
      have hzFront : z ∈ frontier (BS false ∪ BS true ∪ openSegment ℝ M (μ sP)) :=
        ⟨hzcl, fun hz ↦ hzNot (interior_subset hz)⟩
      rw [hSourceFront] at hzFront
      rcases hzFront with hbase | hL
      · by_cases he₁ : z = σ p
        · simpa [he₁] using hSourceContactEndpoints.1
        by_cases he₂ : z = σ q
        · simpa [he₂] using hSourceContactEndpoints.2.1
        exact False.elim (haSub (hChord
          (mem_openSegment_of_ne_left_right (Ne.symm he₁) (Ne.symm he₂) hbase)) hzc)
      · exact ⟨hL, hzc⟩
    · rintro ⟨hL, hzc⟩
      refine ⟨hzc, frontier_subset_closure ?_⟩
      rw [hSourceFront]
      exact Or.inr hL
  have hSourceNonempty : (BS false ∪ BS true ∪ openSegment ℝ M (μ sP)).Nonempty := by
    obtain ⟨x, hx⟩ := (hLiteralHalfGeometry false).2.1
    exact ⟨x, Or.inl (Or.inl hx)⟩
  have hFrontOffCurveInβ : (LF false ∪ LF true) \ range σ ⊆ β := by
    rintro x ⟨hx, hc⟩
    rcases hx with hx | hx
    · obtain ⟨y, z, _, _, _, hxg, _, hg⟩ := hLiteralHalfGapCover false x ⟨hx, hc⟩
      exact hHalfSub false (hg hxg)
    · obtain ⟨y, z, _, _, _, hxg, _, hg⟩ := hLiteralHalfGapCover true x ⟨hx, hc⟩
      exact hHalfSub true (hg hxg)
  have hSourceNorm (Q : ℂ) (hQ : Q ∈ LF false ∪ LF true) : 0 < ‖Q-M‖ := by
    have hhalf (i : Bool) (hQi : Q ∈ LF i) : 0 < ‖Q-M‖ := by
      simp only [hLFFold] at hQi
      rw [hLiteralFront i] at hQi
      cases i
      · exact (hHalfNorm false).2 Q (by simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using hQi)
      · exact (hHalfNorm true).2 Q (by simpa only [triangle, halfHull, endpoint, M, Bool.false_eq_true, ↓reduceIte, Path.source, Path.target] using hQi)
    exact hQ.elim (hhalf false) (hhalf true)
  have hSourceCenterAvoid : ∀ Q ∈ LF false ∪ LF true, Q ≠ M := by
    intro Q hQ he
    have hn := hSourceNorm Q hQ
    simp [he] at hn
  have hSourceFrontInClosure (Q : ℂ) (hQ : Q ∈ LF false ∪ LF true) :
      Q ∈ closure (BS false ∪ BS true ∪ openSegment ℝ M (μ sP)) := by
    rw [hLiteralSweep]
    exact ⟨Q, hQ, 1, by simp [I], by simp⟩
  let cside : ℝ := (star (σ q - σ p) * (μ sP - σ p)).im
  have hcside : cside ≠ 0 := by
    obtain ⟨x, hx⟩ := hSourceNonempty
    have hs := hSourceStrictSide x hx
    change 0 < cside * _ at hs
    intro he
    simp [he] at hs
  have hSourceWeakSide (Q : ℂ) (hQ : Q ∈ LF false ∪ LF true) :
      0 ≤ cside * ((starRingEnd ℂ) W * (Q-M)).im := by
    have hsub : closure (BS false ∪ BS true ∪ openSegment ℝ M (μ sP)) ⊆
        {z | 0 ≤ cside * (star (σ q - σ p) * (z - σ p)).im} :=
      closure_minimal (fun z hz ↦ (hSourceStrictSide z hz).le)
        (isClosed_le continuous_const (by fun_prop))
    have hh := hsub (hSourceFrontInClosure Q hQ)
    simpa only [mem_ofPred_eq, hcoordCross, coord, starRingEnd_apply] using hh
  have hSourceDirInjective : Set.InjOn
      (fun Q : ℂ ↦ (Q-M) / (‖Q-M‖ : ℂ)) (LF false ∪ LF true) := by
    apply HolomorphicAnosov.radial_unique_normalization_injective M _ hSourceCenterAvoid
    intro Q R t he
    have hp := (hLiteralUniqueI Q (hSourceFrontInClosure Q Q.property)
      (hSourceCenterAvoid Q Q.property)).unique
      (y₁ := (Q, (1 : I))) (y₂ := (R, t)) (by simp) he
    exact congrArg Prod.fst hp
  have hSourceDirectionData :
      ∃ ds : ↥(LF false ∪ LF true) ≃ₜ ↥(directions (σ p) (σ q) (μ sP)),
        (∀ Q, ((ds Q : Circle) : ℂ) = ((Q : ℂ)-M) / (‖(Q : ℂ)-M‖ : ℂ)) ∧
        Continuous (fun v ↦ ‖(ds.symm v : ℂ)-M‖) ∧
        ∀ v, 0 < ‖(ds.symm v : ℂ)-M‖ := by
    apply HolomorphicAnosov.compact_front_semicircle_homeomorph W M
      (sub_ne_zero.mpr hD.symm) cside hcside _ hSourceCompact sourceFrontParam
      hSourceCenterAvoid hSourceWeakSide ?_ ?_ hSourceDirInjective
    · rw [hSourceFrontParamEndpoints.1]
      change (σ p - (σ p+σ q)/2) / (‖σ p - (σ p+σ q)/2‖ : ℂ) = _
      rw [(HolomorphicAnosov.cairns_midpoint_normalized_endpoint_directions (σ p) (σ q) hD).1]
      rw [show σ p-σ q = -W by dsimp [W]; ring, norm_neg, neg_div]
    · rw [hSourceFrontParamEndpoints.2]
      exact (HolomorphicAnosov.cairns_midpoint_normalized_endpoint_directions (σ p) (σ q) hD).2
  have hFullFrontOrder (s t u v : I)
      (hs : (sourceFrontParam s : ℂ) = μ u) (ht : (sourceFrontParam t : ℂ) = μ v) :
      (u ≤ v ↔ s ≤ t) := hFullFrontOrder s t u v hs ht
  clear hHalfContact hHalfNorm hHalfSegments hHalfGaps hCaseIIProvider
    hHalfParam hOpenSource hConnectedSource hSourceSubset hSourceFrontier hSourceClosure
    hSourceUnique hLiteralHalfGeometry hLiteralFront hLiteralStar hCaseI hCaseIIdentities
    hCaseIIIdentities hHalfFrontier hHalfNear hHalfComponent
  clear_value sourceFrontParam
  clear * - σ hσ p q α α' hα hα' hα0 hα1 hα'0 hα'1 hCover hMeet a β hChord h M ε τ sP hε hτ hs0 hs1 hP hray μ hμInjective hμrange hμContact hD hcCompact haSub hβSub endpoint LF BS hLFFold hBSFold hRadialExtension hSourceNonempty hSourceOpen hSourceSub hSourceFront hSourceCompact hSourceContactClosed hSourceContactEndpoints hSourceContactSub hSourceCurveMeet hSourceFrontEmbedding hSourceFrontParamEndpoints hSourceFrontRange hSourceGapPairs hSourceGapGeometry hSourceDirectionData hSourceCenterAvoid hLiteralOpenStar hLiteralSweep hLiteralUniqueI sourceFrontParam hFullFrontOrder hFrontOffCurveInβ
  let SourceGaps := {g : I × I | g.1 < g.2 ∧
    μ g.1 ∈ (LF false ∪ LF true) ∩ range σ ∧
    μ g.2 ∈ (LF false ∪ LF true) ∩ range σ ∧
    ∀ t : I, g.1 < t → t < g.2 → μ t ∉ (LF false ∪ LF true) ∩ range σ}
  have hGapMatch (g : SourceGaps) :
      ∃ l r : I, l < r ∧ (sourceFrontParam l : ℂ) ∈ (LF false ∪ LF true) ∩ range σ ∧
        (sourceFrontParam r : ℂ) ∈ (LF false ∪ LF true) ∩ range σ ∧
        (∀ t : I, l < t → t < r → (sourceFrontParam t : ℂ) ∉ (LF false ∪ LF true) ∩ range σ) ∧
        (sourceFrontParam l : ℂ) = μ g.val.1 ∧ (sourceFrontParam r : ℂ) = μ g.val.2 ∧
        openSegment ℝ (μ g.val.1) (μ g.val.2) =
          (fun t : I ↦ (sourceFrontParam t : ℂ)) '' Ioo l r := by
    have hg : (μ g.val.1, μ g.val.2) ∈ gapPairs μ ((LF false ∪ LF true) ∩ range σ) :=
      ⟨g.val.1, g.val.2, g.property.1, g.property.2.1,
        g.property.2.2.1, g.property.2.2.2, rfl⟩
    rw [hSourceGapPairs] at hg
    obtain ⟨l, r, hlr, hl, hr, hgap, he⟩ := hg
    have he1 : (sourceFrontParam l : ℂ) = μ g.val.1 := (congrArg Prod.fst he).symm
    have he2 : (sourceFrontParam r : ℂ) = μ g.val.2 := (congrArg Prod.snd he).symm
    refine ⟨l, r, hlr, hl, hr, hgap, he1, he2, ?_⟩
    rw [← he1, ← he2]
    exact (hSourceGapGeometry l r hlr hl hr hgap).1.symm
  have hGapChordSubset (g : SourceGaps) :
      openSegment ℝ (μ g.val.1) (μ g.val.2) ⊆ (LF false ∪ LF true) \ range σ := by
    obtain ⟨l, r, _, _, _, hg, _, _, he⟩ := hGapMatch g
    rw [he]
    rintro x ⟨t, ht, rfl⟩
    exact ⟨(sourceFrontParam t).property, fun hc ↦
      hg t ht.1 ht.2 ⟨(sourceFrontParam t).property, hc⟩⟩
  have hGapChordsDisjoint : Pairwise (fun g h : SourceGaps ↦
      Disjoint (openSegment ℝ (μ g.val.1) (μ g.val.2))
        (openSegment ℝ (μ h.val.1) (μ h.val.2))) :=
    HolomorphicAnosov.matching_contact_gap_chords_disjoint μ
      (fun t : I ↦ (sourceFrontParam t : ℂ)) hμInjective hSourceFrontEmbedding.injective
      (fun t ↦ μ t ∈ (LF false ∪ LF true) ∩ range σ)
      (fun t ↦ (sourceFrontParam t : ℂ) ∈ (LF false ∪ LF true) ∩ range σ) hGapMatch
  have hα0 : α (0 : I) = p := hα0
  have hα1 : α (1 : I) = q := hα1
  have hμEval (t : I) : μ t = σ (α t) := rfl
  let sourceArcs : Option SourceGaps → Set Circle := fun i ↦ match i with
    | none => α' '' Ioo 0 1
    | some g => α '' Ioo g.val.1 g.val.2
  let sourceLeft : Option SourceGaps → Circle := fun i ↦ match i with
    | none => α 0
    | some g => α g.val.1
  let sourceRight : Option SourceGaps → Circle := fun i ↦ match i with
    | none => α 1
    | some g => α g.val.2
  obtain ⟨hGapCount, hArcData, hArcDisjoint⟩ := HolomorphicAnosov.embedded_circle_contact_arc_family
    α α' hα hα' hCover (hα'0.trans hα0.symm) (hα'1.trans hα1.symm)
    (by simpa [hα0, hα1] using hMeet)
    (fun t ↦ μ t ∈ (LF false ∪ LF true) ∩ range σ)
  let instSourceGapsCountable : Countable SourceGaps := hGapCount
  have hAllChordsAvoid (i : Option SourceGaps) :
      Disjoint (openSegment ℝ (σ (sourceLeft i)) (σ (sourceRight i))) (range σ) := by
    cases i with
    | none =>
      change Disjoint (openSegment ℝ (σ (α 0)) (σ (α 1))) (range σ)
      rw [hα0, hα1]
      exact disjoint_left.mpr (fun _ hx hc ↦ haSub (hChord hx) hc)
    | some g => exact disjoint_left.mpr (fun _ hx hc ↦ (hGapChordSubset g hx).2 hc)
  have hAllChordsDisjoint : Pairwise (fun i j : Option SourceGaps ↦
      Disjoint (openSegment ℝ (σ (sourceLeft i)) (σ (sourceRight i)))
        (openSegment ℝ (σ (sourceLeft j)) (σ (sourceRight j)))) := by
    have hbase (g : SourceGaps) : Disjoint (openSegment ℝ (σ p) (σ q))
        (openSegment ℝ (μ g.val.1) (μ g.val.2)) :=
      disjoint_left.mpr (fun x hx hg ↦ (hβSub (hFrontOffCurveInβ (hGapChordSubset g hg))).2 hx)
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some g => simpa [sourceLeft, sourceRight, hμEval, hα0, hα1] using hbase g
    | some g =>
      cases j with
      | none => simpa [sourceLeft, sourceRight, hμEval, hα0, hα1] using (hbase g).symm
      | some g' => exact hGapChordsDisjoint (fun he ↦ hij (congrArg some he))
  obtain ⟨sourceSkeletonMap, hSkeletonCurve, hSkeletonAffine⟩ :=
    HolomorphicAnosov.accumulatingChordContinuity σ hσ h sourceArcs sourceLeft sourceRight
      (fun i ↦ (hArcData i).1) (fun i ↦ (hArcData i).2.1)
      (fun i ↦ (hArcData i).2.2.1) (fun i ↦ (hArcData i).2.2.2.1)
      (fun i ↦ (hArcData i).2.2.2.2) hArcDisjoint hAllChordsAvoid hAllChordsDisjoint
  have hSourceSkeletonSet : range σ ∪ ⋃ i : Option SourceGaps,
      segment ℝ (σ (sourceLeft i)) (σ (sourceRight i)) =
        range σ ∪ segment ℝ (σ p) (σ q) ∪ (LF false ∪ LF true) := by
    ext x
    constructor
    · rintro (hc | hx)
      · exact Or.inl (Or.inl hc)
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      cases i with
      | none => exact Or.inl (Or.inr (by simpa [sourceLeft, sourceRight, hμEval, hα0, hα1] using hi))
      | some g =>
        apply Or.inr
        change x ∈ segment ℝ (μ g.val.1) (μ g.val.2) at hi
        by_cases he1 : x = μ g.val.1
        · exact he1 ▸ g.property.2.1.1
        by_cases he2 : x = μ g.val.2
        · exact he2 ▸ g.property.2.2.1.1
        exact (hGapChordSubset g (mem_openSegment_of_ne_left_right (Ne.symm he1) (Ne.symm he2) hi)).1
    · rintro ((hc | hb) | hL)
      · exact Or.inl hc
      · apply Or.inr
        apply mem_iUnion.mpr ⟨none, ?_⟩
        simpa [sourceLeft, sourceRight, hμEval, hα0, hα1] using hb
      by_cases hc : x ∈ range σ
      · exact Or.inl hc
      have hx : x ∈ range (fun t : I ↦ (sourceFrontParam t : ℂ)) \
          ((LF false ∪ LF true) ∩ range σ) := by
        rw [hSourceFrontRange]
        exact ⟨hL, fun hh ↦ hc hh.2⟩
      obtain ⟨l, r, hlr, hl, hr, hg, hcomp⟩ :=
        HolomorphicAnosov.embedded_interval_contact_gap
          (fun t : I ↦ (sourceFrontParam t : ℂ)) hSourceFrontEmbedding _ hSourceContactClosed
          (by simpa only [hSourceFrontParamEndpoints.1] using hSourceContactEndpoints.1)
          (by simpa only [hSourceFrontParamEndpoints.2] using hSourceContactEndpoints.2.1) x hx
      have hxgap : x ∈ (fun t : I ↦ (sourceFrontParam t : ℂ)) '' Ioo l r :=
        hcomp ▸ mem_connectedComponentIn hx
      have hp : ((sourceFrontParam l : ℂ), (sourceFrontParam r : ℂ)) ∈
          gapPairs μ ((LF false ∪ LF true) ∩ range σ) := by
        rw [hSourceGapPairs]
        exact ⟨l, r, hlr, hl, hr, hg, rfl⟩
      obtain ⟨u, v, huv, hu, hv, huvGap, he⟩ := hp
      let g : SourceGaps := ⟨(u,v), huv, hu, hv, huvGap⟩
      have he1 : (sourceFrontParam l : ℂ) = μ u := congrArg Prod.fst he
      have he2 : (sourceFrontParam r : ℂ) = μ v := congrArg Prod.snd he
      have hseg := (hSourceGapGeometry l r hlr hl hr hg).1 ▸ hxgap
      apply Or.inr
      apply mem_iUnion.mpr ⟨some g, ?_⟩
      change x ∈ segment ℝ (μ u) (μ v)
      exact openSegment_subset_segment ℝ _ _ (by simpa only [he1, he2] using hseg)
  let sourceX := range σ ∪ ⋃ i : Option SourceGaps,
    segment ℝ (σ (sourceLeft i)) (σ (sourceRight i))
  let E₁ : ℂ := h ⟨σ p, ⟨p,rfl⟩⟩
  let E₂ : ℂ := h ⟨σ q, ⟨q,rfl⟩⟩
  let circleK := range (fun z : Circle ↦ (z : ℂ))
  let targetY := circleK ∪ ⋃ i : Option SourceGaps,
    segment ℝ (h ⟨σ (sourceLeft i), ⟨sourceLeft i,rfl⟩⟩ : ℂ)
      (h ⟨σ (sourceRight i), ⟨sourceRight i,rfl⟩⟩ : ℂ)
  have hLX : LF false ∪ LF true ⊆ sourceX := by
    rw [show sourceX = _ from hSourceSkeletonSet]
    exact subset_union_right
  let hCircle : range σ ≃ₜ circleK :=
    h.trans Topology.IsEmbedding.subtypeVal.toHomeomorph
  obtain ⟨ν, frontTargetMap, hνCompact, hFrontTargetMap, hνContact⟩ :=
    HolomorphicAnosov.compact_front_skeleton_transport (range σ) (LF false ∪ LF true)
      sourceX circleK targetY hSourceCompact subset_union_left hLX
      hCircle sourceSkeletonMap hSkeletonCurve
  let targetFrontParam : I ≃ₜ ν := sourceFrontParam.trans frontTargetMap
  have hSkeletonBase (t : ℝ) (ht : t ∈ Icc 0 1) (x : sourceX)
      (hx : (x : ℂ) = (1-t) • σ p + t • σ q) :
      (sourceSkeletonMap x : ℂ) = (1-t) • E₁ + t • E₂ := by
    simpa [sourceLeft, sourceRight, hμEval, hα0, hα1, E₁, E₂] using
      hSkeletonAffine none t x ht (by simpa [sourceLeft, sourceRight, hμEval, hα0, hα1] using hx)
  have hTargetSkeletonSet : targetY = circleK ∪ segment ℝ E₁ E₂ ∪ ν := by
    ext y
    constructor
    · intro hy
      obtain ⟨x,hx⟩ := sourceSkeletonMap.surjective ⟨y,hy⟩
      have hx' : (x : ℂ) ∈ range σ ∪ segment ℝ (σ p) (σ q) ∪ (LF false ∪ LF true) :=
        hSourceSkeletonSet ▸ x.property
      have he : (sourceSkeletonMap x : ℂ) = y := congrArg Subtype.val hx
      rcases hx' with (hc | hb) | hL
      · exact Or.inl (Or.inl ⟨h ⟨x,hc⟩,(hSkeletonCurve x hc).symm.trans he⟩)
      · rw [segment_eq_image_lineMap] at hb
        obtain ⟨t,ht,het⟩ := hb
        have hf := hSkeletonBase t ht x (by simpa [AffineMap.lineMap_apply_module] using het.symm)
        apply Or.inl ∘ Or.inr
        rw [segment_eq_image_lineMap]
        exact ⟨t,ht,(by simpa [AffineMap.lineMap_apply_module] using hf.symm.trans he)⟩
      · have hh := hFrontTargetMap ⟨x,hL⟩
        exact Or.inr (by rw [← he, ← hh]; exact (frontTargetMap ⟨x,hL⟩).property)
    · rintro ((hk | hb) | hν)
      · exact Or.inl hk
      · apply Or.inr
        apply mem_iUnion.mpr ⟨none,?_⟩
        simpa [sourceLeft,sourceRight,hμEval,hα0,hα1,E₁,E₂] using hb
      · obtain ⟨Q,hQ⟩ := frontTargetMap.surjective ⟨y,hν⟩
        have he : (frontTargetMap Q : ℂ) = y := congrArg Subtype.val hQ
        rw [hFrontTargetMap Q] at he
        exact he ▸ (sourceSkeletonMap ⟨Q,hLX Q.property⟩).property
  let H₀ : ↥(range σ ∪ segment ℝ (σ p) (σ q) ∪ (LF false ∪ LF true)) ≃ₜ
      ↥(circleK ∪ segment ℝ E₁ E₂ ∪ ν) :=
    (Homeomorph.setCongr hSourceSkeletonSet.symm).trans
      (sourceSkeletonMap.trans (Homeomorph.setCongr hTargetSkeletonSet))
  have hSourceFrontCovered (Q : ↥(LF false ∪ LF true)) :
      (Q : ℂ) ∈ range σ ∨ ∃ g : SourceGaps, (Q : ℂ) ∈ segment ℝ (μ g.val.1) (μ g.val.2) := by
    by_cases hc : (Q : ℂ) ∈ range σ
    · exact Or.inl hc
    apply Or.inr
    obtain ⟨i,hi⟩ := mem_iUnion.mp ((hLX Q.property).resolve_left hc)
    cases i with
    | none =>
      have hb : (Q : ℂ) ∈ segment ℝ (σ p) (σ q) := by
        simpa [sourceLeft,sourceRight,hμEval,hα0,hα1] using hi
      have hop : (Q : ℂ) ∈ openSegment ℝ (σ p) (σ q) :=
        mem_openSegment_of_ne_left_right
          (fun he ↦ hc (he ▸ mem_range_self p)) (fun he ↦ hc (he ▸ mem_range_self q)) hb
      exact ((hβSub (hFrontOffCurveInβ ⟨Q.property,hc⟩)).2 hop).elim
    | some g => exact ⟨g,hi⟩
  let targetContact := Subtype.val '' hCircle '' {x : range σ | (x : ℂ) ∈ LF false ∪ LF true}
  let gapLeft : SourceGaps → ℂ := fun g ↦ h ⟨μ g.val.1,⟨α g.val.1,rfl⟩⟩
  let gapRight : SourceGaps → ℂ := fun g ↦ h ⟨μ g.val.2,⟨α g.val.2,rfl⟩⟩
  have hTargetFrontCover : ν ⊆ targetContact ∪ ⋃ g : SourceGaps, segment ℝ (gapLeft g) (gapRight g) := by
    intro y hy
    obtain ⟨Q,hQ⟩ := frontTargetMap.surjective ⟨y,hy⟩
    have hQy : (frontTargetMap Q : ℂ) = y := congrArg Subtype.val hQ
    have hHy : (sourceSkeletonMap ⟨Q,hLX Q.property⟩ : ℂ) = y :=
      (hFrontTargetMap Q).symm.trans hQy
    rcases hSourceFrontCovered Q with hc | ⟨g,hg⟩
    · apply Or.inl
      refine ⟨hCircle ⟨Q,hc⟩,⟨⟨Q,hc⟩,Q.property,rfl⟩,?_⟩
      exact (hSkeletonCurve ⟨Q,hLX Q.property⟩ hc).symm.trans hHy
    · apply Or.inr
      rw [segment_eq_image_lineMap] at hg
      obtain ⟨t,ht,he⟩ := hg
      have hline := hSkeletonAffine (some g) t ⟨Q,hLX Q.property⟩ ht
        (by simpa [sourceLeft,sourceRight,hμEval,AffineMap.lineMap_apply_module] using he.symm)
      apply mem_iUnion.mpr ⟨g,?_⟩
      rw [segment_eq_image_lineMap]
      exact ⟨t,ht,(by simpa [gapLeft,gapRight,sourceLeft,sourceRight,hμEval,AffineMap.lineMap_apply_module]
        using hline.symm.trans hHy)⟩
  let gCircle : Circle → Circle := fun p ↦ h ⟨σ p,⟨p,rfl⟩⟩
  have hgCircle : Continuous gCircle := h.continuous.comp
    (hσ.continuous.subtype_mk (fun p ↦ ⟨p,rfl⟩))
  have hgCircleInj : Function.Injective gCircle := by
    intro u v he
    exact hσ.injective (congrArg Subtype.val (h.injective he))
  have hContactOutside (g : SourceGaps) (p : Circle) (hp : σ p ∈ LF false ∪ LF true) :
      p ∉ sourceArcs (some g) := by
    rintro ⟨t,ht,he⟩
    apply g.property.2.2.2 t ht.1 ht.2
    change σ (α t) ∈ (LF false ∪ LF true) ∩ range σ
    rw [he]
    exact ⟨hp,mem_range_self p⟩
  have hTargetContactSupport (f : ℂ → ℝ)
      (hf : ∀ p : Circle, σ p ∈ LF false ∪ LF true → 0 ≤ f (gCircle p)) :
      ∀ y ∈ targetContact, 0 ≤ f y := by
    rintro y ⟨z,⟨x,hx,rfl⟩,rfl⟩
    obtain ⟨p,hp⟩ := x.property
    have he : x = ⟨σ p,mem_range_self p⟩ := Subtype.ext hp.symm
    subst x
    exact hf p hx
  have hTargetFrontSupport (f : ℂ → ℝ)
      (haff : ∀ x y : ℂ, ∀ t : ℝ, f ((1-t) • x+t • y) = (1-t)*f x+t*f y)
      (hf : ∀ p : Circle, σ p ∈ LF false ∪ LF true → 0 ≤ f (gCircle p)) :
      ∀ y ∈ ν, 0 ≤ f y := by
    intro y hy
    rcases hTargetFrontCover hy with hc | hg
    · exact hTargetContactSupport f hf y hc
    obtain ⟨g,hg⟩ := mem_iUnion.mp hg
    rw [segment_eq_image_lineMap] at hg
    obtain ⟨t,ht,rfl⟩ := hg
    rw [AffineMap.lineMap_apply_module,haff]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr ht.2) (hf (α g.val.1) g.property.2.1.1))
      (mul_nonneg ht.1 (hf (α g.val.2) g.property.2.2.1.1))
  have hGapSupport (g : SourceGaps) : ∃ f : ℂ → ℝ,
      f (gapLeft g) = 0 ∧ f (gapRight g) = 0 ∧
      (∀ x y : ℂ, ∀ t : ℝ, f ((1-t) • x+t • y) = (1-t)*f x+t*f y) ∧
      (∀ y ∈ ν, 0 ≤ f y) ∧ 0 < f ((E₁+E₂)/2) := by
    obtain ⟨f,hfl,hfr,haff,hn,hp⟩ := HolomorphicAnosov.circle_open_arc_complement_support
      (sourceArcs (some g)) (sourceLeft (some g)) (sourceRight (some g))
      (hArcData (some g)).1 (hArcData (some g)).2.1
      (hArcData (some g)).2.2.2.1 (hArcData (some g)).2.2.2.2
      gCircle hgCircle hgCircleInj
    have hfC : ∀ p : Circle, σ p ∈ LF false ∪ LF true → 0 ≤ f (gCircle p) :=
      fun p hp ↦ hn p (hContactOutside g p hp)
    have hn1 : 0 ≤ f E₁ := hfC p hSourceContactEndpoints.1.1
    have hn2 : 0 ≤ f E₂ := hfC q hSourceContactEndpoints.2.1.1
    have hnotWhole : g.val.1 ≠ 0 ∨ g.val.2 ≠ 1 := by
      by_cases h0 : g.val.1 = 0
      · right
        intro h1
        exact g.property.2.2.2 sP (by simpa [h0] using hs0) (by simpa [h1] using hs1)
          hSourceContactEndpoints.2.2
      · exact Or.inl h0
    have hpositive : 0 < f E₁ ∨ 0 < f E₂ := by
      rcases hnotWhole with h0 | h1
      · left
        apply hp p (hContactOutside g p hSourceContactEndpoints.1.1)
        · intro he
          exact h0 (hα.injective (he.symm.trans hα0.symm))
        · intro he
          have hg0 : g.val.2 = (0 : I) := hα.injective (he.symm.trans hα0.symm)
          have hlt : (0 : I) < g.val.2 := lt_of_le_of_lt g.val.1.property.1 g.property.1
          exact hlt.ne hg0.symm
      · right
        apply hp q (hContactOutside g q hSourceContactEndpoints.2.1.1)
        · intro he
          have hg1 : g.val.1 = (1 : I) := hα.injective (he.symm.trans hα1.symm)
          have hlt : g.val.1 < (1 : I) := lt_of_lt_of_le g.property.1 g.val.2.property.2
          exact hlt.ne hg1
        · intro he
          exact h1 (hα.injective (he.symm.trans hα1.symm))
    refine ⟨f,hfl,hfr,haff,hTargetFrontSupport f haff hfC,?_⟩
    have hm : (E₁+E₂)/2 = (1-(1/2:ℝ)) • E₁ + (1/2:ℝ) • E₂ := by
      simp only [Complex.real_smul]
      push_cast
      ring
    rw [hm,haff]
    rcases hpositive with hp | hp <;> nlinarith
  have hTargetNorm : ∀ y ∈ ν, ‖y‖ ≤ 1 := by
    intro y hy
    rcases hTargetFrontCover hy with hc | hg
    · rcases hc with ⟨z,_,rfl⟩
      obtain ⟨p,hp⟩ := z.property
      rw [← hp]
      exact (Circle.norm_coe p).le
    · obtain ⟨g,hg⟩ := mem_iUnion.mp hg
      have hc := (convex_closedBall (0 : ℂ) (1 : ℝ)).segment_subset
        (show gapLeft g ∈ Metric.closedBall 0 1 by simp [gapLeft,Metric.mem_closedBall])
        (show gapRight g ∈ Metric.closedBall 0 1 by simp [gapRight,Metric.mem_closedBall]) hg
      simpa [Metric.mem_closedBall] using hc
  have hTargetEneq : E₁ ≠ E₂ := by
    intro he
    have hpq := hgCircleInj (Circle.coe_injective he)
    have hh := hα.injective (hα0.trans (hpq.trans hα1.symm))
    exact (show (0 : I) ≠ 1 by norm_num) hh
  let N : ℂ := (E₁+E₂)/2
  have hTargetMidNorm : ‖N‖ < 1 :=
    HolomorphicAnosov.cairns_midpoint_norm_lt_one_of_circle_distinct E₁ E₂
      (Circle.norm_coe _) (Circle.norm_coe _) hTargetEneq
  have hTargetSupport (y : ℂ) (hy : y ∈ ν) : ‖y‖ = 1 ∨ ∃ f : ℂ → ℝ,
      f y = 0 ∧ 0 < f N ∧ (∀ R ∈ ν, 0 ≤ f R) ∧
      ∀ (R : ℂ) (t : ℝ), f ((1-t) • N+t • R) = (1-t)*f N+t*f R := by
    rcases hTargetFrontCover hy with hc | hg
    · left
      rcases hc with ⟨z,_,rfl⟩
      obtain ⟨p,hp⟩ := z.property
      rw [← hp]
      exact Circle.norm_coe p
    · right
      obtain ⟨g,hg⟩ := mem_iUnion.mp hg
      obtain ⟨f,hfl,hfr,haff,hf,hmid⟩ := hGapSupport g
      refine ⟨f,?_,hmid,hf,haff N⟩
      rw [segment_eq_image_lineMap] at hg
      obtain ⟨t,_,rfl⟩ := hg
      rw [AffineMap.lineMap_apply_module,haff,hfl,hfr]
      ring
  obtain ⟨hTargetCenterAvoid,hTargetDirInjective⟩ :=
    HolomorphicAnosov.supporting_front_normalization_injective ν N hTargetMidNorm hTargetNorm hTargetSupport
  have hTargetFrontEndpoints : (targetFrontParam 0 : ℂ) = E₁ ∧ (targetFrontParam 1 : ℂ) = E₂ := by
    constructor
    · change (frontTargetMap (sourceFrontParam 0) : ℂ) = E₁
      rw [hFrontTargetMap]
      have hc : (sourceFrontParam 0 : ℂ) ∈ range σ := by
        rw [hSourceFrontParamEndpoints.1]
        exact mem_range_self p
      rw [hSkeletonCurve _ hc]
      have he : (⟨(sourceFrontParam 0 : ℂ),hc⟩ : range σ) = ⟨σ p,mem_range_self p⟩ :=
        Subtype.ext hSourceFrontParamEndpoints.1
      rw [he]
    · change (frontTargetMap (sourceFrontParam 1) : ℂ) = E₂
      rw [hFrontTargetMap]
      have hc : (sourceFrontParam 1 : ℂ) ∈ range σ := by
        rw [hSourceFrontParamEndpoints.2]
        exact mem_range_self q
      rw [hSkeletonCurve _ hc]
      have he : (⟨(sourceFrontParam 1 : ℂ),hc⟩ : range σ) = ⟨σ q,mem_range_self q⟩ :=
        Subtype.ext hSourceFrontParamEndpoints.2
      rw [he]
  let Eₚ : ℂ := gCircle (α sP)
  let targetCross : ℂ → ℝ := fun z ↦ ((starRingEnd ℂ) (E₂-E₁)*(z-E₁)).im
  let targetSide : ℝ := targetCross Eₚ
  let targetArc : I → Circle := fun t ↦ gCircle (α t)
  obtain ⟨δ,hδ,hTargetArcSide,hTargetArcStrict⟩ :=
    HolomorphicAnosov.embedded_circle_arc_signed_side targetArc
      (hgCircle.comp hα.continuous) (hgCircleInj.comp hα.injective)
  have hTargetArcWeak (t : I) : 0 ≤ δ * targetCross (gCircle (α t)) := by
    simpa [targetArc,targetCross,E₁,E₂,gCircle,hα0,hα1] using hTargetArcSide t
  have hTargetSidePos : 0 < δ*targetSide := by
    simpa [targetArc,targetCross,targetSide,Eₚ,E₁,E₂,gCircle,hα0,hα1] using
      hTargetArcStrict sP ⟨hs0,hs1⟩
  have hTargetSideNe : targetSide ≠ 0 := by
    intro he
    simp [he] at hTargetSidePos
  have hTargetCrossAffine (x y : ℂ) (t : ℝ) :
      targetSide*targetCross ((1-t) • x+t • y) =
        (1-t)*(targetSide*targetCross x)+t*(targetSide*targetCross y) := by
    simp only [targetCross,Complex.mul_im,Complex.conj_re,Complex.conj_im,
      Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
      Complex.smul_re,Complex.smul_im,smul_eq_mul]
    ring
  have hTargetWeakSide (y : ℂ) (hy : y ∈ ν) : 0 ≤ targetSide*targetCross y := by
    apply hTargetFrontSupport (fun z ↦ targetSide*targetCross z) hTargetCrossAffine ?_ y hy
    intro p hp
    obtain ⟨t,ht⟩ := hSourceContactSub ⟨hp,mem_range_self p⟩
    have ht' : α t = p := hσ.injective ht
    rw [← ht']
    have hw := hTargetArcWeak t
    rcases hδ with rfl | rfl
    · simp only [one_mul] at hw hTargetSidePos
      exact mul_nonneg hTargetSidePos.le hw
    · have hn : targetSide ≤ 0 := by linarith
      have hm : targetCross (gCircle (α t)) ≤ 0 := by linarith
      exact mul_nonneg_of_nonpos_of_nonpos hn hm
  have hTargetCrossCenter (y : ℂ) :
      ((starRingEnd ℂ) (E₂-E₁)*(y-N)).im = targetCross y := by
    have he : (starRingEnd ℂ) (E₂-E₁)*(y-N) =
        (starRingEnd ℂ) (E₂-E₁)*(y-E₁) - (1/2:ℂ)*((starRingEnd ℂ) (E₂-E₁)*(E₂-E₁)) := by
      dsimp [N]
      ring
    rw [he,← Complex.normSq_eq_conj_mul_self]
    simp [targetCross]
  have hTargetDirectionData :
      ∃ dt : ν ≃ₜ {v : Circle | 0 ≤ targetSide*((starRingEnd ℂ) (E₂-E₁)*(v:ℂ)).im},
        (∀ Q : ν, ((dt Q : Circle) : ℂ) = ((Q:ℂ)-N)/(‖(Q:ℂ)-N‖:ℂ)) ∧
        Continuous (fun v ↦ ‖(dt.symm v : ℂ)-N‖) ∧
        ∀ v, 0 < ‖(dt.symm v : ℂ)-N‖ := by
    apply HolomorphicAnosov.compact_front_semicircle_homeomorph (E₂-E₁) N
      (sub_ne_zero.mpr hTargetEneq.symm) targetSide hTargetSideNe ν hνCompact targetFrontParam
      hTargetCenterAvoid ?_ ?_ ?_ hTargetDirInjective
    · intro y hy
      rw [hTargetCrossCenter]
      exact hTargetWeakSide y hy
    · rw [hTargetFrontEndpoints.1]
      rw [(HolomorphicAnosov.cairns_midpoint_normalized_endpoint_directions E₁ E₂ hTargetEneq).1]
      rw [show E₁-E₂ = -(E₂-E₁) by ring,norm_neg,neg_div]
    · rw [hTargetFrontEndpoints.2]
      exact (HolomorphicAnosov.cairns_midpoint_normalized_endpoint_directions E₁ E₂ hTargetEneq).2
  have hTargetContactOriginal (t : I) : (gCircle (α t) : ℂ) ∈ targetContact ↔
      μ t ∈ (LF false ∪ LF true) ∩ range σ := by
    constructor
    · rintro ⟨y,⟨x,hx,rfl⟩,he⟩
      have hxEq : x = ⟨μ t,⟨α t,rfl⟩⟩ := hCircle.injective (Subtype.ext he)
      exact ⟨by simpa only [hxEq,mem_ofPred_eq] using hx,⟨α t,rfl⟩⟩
    · intro ht
      exact ⟨hCircle ⟨μ t,ht.2⟩,⟨⟨μ t,ht.2⟩,ht.1,rfl⟩,rfl⟩
  have hTargetContactFront (t : I) : (targetFrontParam t : ℂ) ∈ targetContact ↔
      (sourceFrontParam t : ℂ) ∈ (LF false ∪ LF true) ∩ range σ := by
    constructor
    · rintro ⟨y,⟨x,hx,rfl⟩,he⟩
      have heH : (sourceSkeletonMap ⟨x,Or.inl x.property⟩ : ℂ) =
          (sourceSkeletonMap ⟨sourceFrontParam t,hLX (sourceFrontParam t).property⟩ : ℂ) :=
        (hSkeletonCurve _ x.property).trans (he.trans (hFrontTargetMap (sourceFrontParam t)))
      have heX : (x : ℂ) = sourceFrontParam t :=
        congrArg (fun z : sourceX ↦ (z:ℂ)) (sourceSkeletonMap.injective (Subtype.ext heH))
      exact ⟨(sourceFrontParam t).property,heX ▸ x.property⟩
    · intro ht
      refine ⟨hCircle ⟨sourceFrontParam t,ht.2⟩,⟨⟨sourceFrontParam t,ht.2⟩,ht.1,rfl⟩,?_⟩
      exact (hSkeletonCurve _ ht.2).symm.trans (hFrontTargetMap (sourceFrontParam t)).symm
  have hTargetCrossEquality (s t : I) : μ s = (sourceFrontParam t : ℂ) ↔
      (gCircle (α s) : ℂ) = targetFrontParam t := by
    have he1 : (sourceSkeletonMap ⟨μ s,Or.inl ⟨α s,rfl⟩⟩ : ℂ) = gCircle (α s) :=
      hSkeletonCurve _ ⟨α s,rfl⟩
    have he2 : (sourceSkeletonMap ⟨sourceFrontParam t,hLX (sourceFrontParam t).property⟩ : ℂ) =
        targetFrontParam t := (hFrontTargetMap (sourceFrontParam t)).symm
    constructor
    · intro he
      have hsub : (⟨μ s,Or.inl ⟨α s,rfl⟩⟩ : sourceX) =
          ⟨sourceFrontParam t,hLX (sourceFrontParam t).property⟩ := Subtype.ext he
      exact he1.symm.trans ((congrArg (fun x : sourceX ↦ (sourceSkeletonMap x:ℂ)) hsub).trans he2)
    · intro he
      exact congrArg (fun x : sourceX ↦ (x:ℂ))
        (sourceSkeletonMap.injective (Subtype.ext (he1.trans (he.trans he2.symm))))
  have hTargetGapPairs : gapPairs (fun t : I ↦ (gCircle (α t) : ℂ)) targetContact =
      gapPairs (fun t : I ↦ (targetFrontParam t : ℂ)) targetContact :=
    gap_pairs_transport μ (fun t : I ↦ (sourceFrontParam t:ℂ))
      (fun t : I ↦ (gCircle (α t):ℂ)) (fun t : I ↦ (targetFrontParam t:ℂ))
      ((LF false ∪ LF true) ∩ range σ) targetContact hSourceGapPairs
      hTargetContactOriginal hTargetContactFront hTargetCrossEquality
  have hTargetGapGeometry (l r : I) (hlr : l < r)
      (hl : (targetFrontParam l:ℂ) ∈ targetContact) (hr : (targetFrontParam r:ℂ) ∈ targetContact)
      (hgap : ∀ t : I, l < t → t < r → (targetFrontParam t:ℂ) ∉ targetContact) :
      (fun t : I ↦ (targetFrontParam t:ℂ)) '' Ioo l r =
        openSegment ℝ (targetFrontParam l:ℂ) (targetFrontParam r:ℂ) := by
    have hsl := (hTargetContactFront l).mp hl
    have hsr := (hTargetContactFront r).mp hr
    have hsgap : ∀ t : I, l < t → t < r → (sourceFrontParam t:ℂ) ∉
        (LF false ∪ LF true) ∩ range σ :=
      fun t hlt htr ht ↦ hgap t hlt htr ((hTargetContactFront t).mpr ht)
    have hpair : ((sourceFrontParam l:ℂ),(sourceFrontParam r:ℂ)) ∈
        gapPairs μ ((LF false ∪ LF true) ∩ range σ) := by
      rw [hSourceGapPairs]
      exact ⟨l,r,hlr,hsl,hsr,hsgap,rfl⟩
    obtain ⟨u,v,huv,hu,hv,huvgap,he⟩ := hpair
    let g : SourceGaps := ⟨(u,v),huv,hu,hv,huvgap⟩
    have hel : (sourceFrontParam l:ℂ) = μ u := congrArg Prod.fst he
    have her : (sourceFrontParam r:ℂ) = μ v := congrArg Prod.snd he
    have htl : (targetFrontParam l:ℂ) = gapLeft g := (hTargetCrossEquality u l).mp hel.symm |>.symm
    have htr : (targetFrontParam r:ℂ) = gapRight g := (hTargetCrossEquality v r).mp her.symm |>.symm
    have hsrc := (hSourceGapGeometry l r hlr hsl hsr hsgap).1
    rw [hel,her] at hsrc
    have hmap (t : ℝ) (ht : t ∈ Ioo 0 1) :
        ∃ s ∈ Ioo l r, (targetFrontParam s:ℂ) = (1-t) • gapLeft g+t • gapRight g := by
      have hm : (1-t) • μ u+t • μ v ∈ openSegment ℝ (μ u) (μ v) :=
        ⟨1-t,t,sub_pos.mpr ht.2,ht.1,by ring,rfl⟩
      obtain ⟨s,hs,hse⟩ := hsrc.symm ▸ hm
      refine ⟨s,hs,?_⟩
      have hh := hSkeletonAffine (some g) t ⟨sourceFrontParam s,hLX (sourceFrontParam s).property⟩
        ⟨ht.1.le,ht.2.le⟩ hse
      exact (hFrontTargetMap (sourceFrontParam s)).trans hh
    apply subset_antisymm
    · rintro z ⟨s,hs,rfl⟩
      have hm : (sourceFrontParam s:ℂ) ∈ openSegment ℝ (μ u) (μ v) := hsrc ▸ mem_image_of_mem _ hs
      obtain ⟨a,b,ha,hb,hab,heab⟩ := hm
      have ht : b ∈ Ioo (0:ℝ) 1 := ⟨hb,by linarith⟩
      have ha' : a = 1-b := by linarith
      have hsEq : (sourceFrontParam s:ℂ) = (1-b) • μ u+b • μ v := by simpa [ha'] using heab.symm
      have hh := hSkeletonAffine (some g) b ⟨sourceFrontParam s,hLX (sourceFrontParam s).property⟩
        ⟨ht.1.le,ht.2.le⟩ hsEq
      have hv : (targetFrontParam s:ℂ) = (1-b) • gapLeft g+b • gapRight g :=
        (hFrontTargetMap (sourceFrontParam s)).trans hh
      change (targetFrontParam s:ℂ) ∈ openSegment ℝ (targetFrontParam l:ℂ) (targetFrontParam r:ℂ)
      rw [htl,htr,hv]
      exact ⟨1-b,b,sub_pos.mpr ht.2,ht.1,by ring,rfl⟩
    · intro z hz
      rw [htl,htr] at hz
      obtain ⟨a,b,ha,hb,hab,rfl⟩ := hz
      obtain ⟨s,hs,he⟩ := hmap b ⟨hb,by linarith⟩
      exact ⟨s,hs,by simpa [show a = 1-b by linarith] using he⟩
  obtain ⟨dt,hdt,hdtContinuous,hdtPositive⟩ := hTargetDirectionData
  have hTargetEndpointMem : E₁ ∈ ν ∧ E₂ ∈ ν := by
    constructor
    · exact hTargetFrontEndpoints.1 ▸ (targetFrontParam 0).property
    · exact hTargetFrontEndpoints.2 ▸ (targetFrontParam 1).property
  obtain ⟨hγNonempty,hγOpen,hγFrontier,hγClosure,hγUnique,_,_⟩ :=
    HolomorphicAnosov.cairns_target_radial_star_extension E₁ E₂ Eₚ ν hνCompact hTargetEneq
      hTargetSideNe hTargetEndpointMem.1 hTargetEndpointMem.2
      (fun hn ↦ hTargetCenterAvoid N hn rfl) dt hdt
  let γ := openStar E₁ E₂ Eₚ N ν
  have hγBallSide : γ ⊆ Metric.ball (0:ℂ) 1 ∩ {z | 0 < targetSide*targetCross z} := by
    rintro z ⟨Q,hQ,t,ht,he,hside⟩
    refine ⟨?_,hside⟩
    apply openSegment_subset_ball_of_ne
      (show N ∈ Metric.closedBall 0 1 by simpa [Metric.mem_closedBall] using hTargetMidNorm.le)
      (show Q ∈ Metric.closedBall 0 1 by simpa [Metric.mem_closedBall] using hTargetNorm Q hQ)
      (Ne.symm (hTargetCenterAvoid Q hQ))
    exact ⟨1-t,t,sub_pos.mpr ht.2,ht.1,by ring,he.symm⟩
  have hTargetSweepContact : circleK ∩ sweep N ν = targetContact := by
    calc
      circleK ∩ sweep N ν = circleK ∩ ν :=
        HolomorphicAnosov.unit_circle_contact_radial_sweep ν N hTargetMidNorm hTargetNorm
      _ = targetContact := (inter_comm circleK ν).trans hνContact
  have hTargetGapGeometryFull (l r : I) (hlr : l < r)
      (hl : (targetFrontParam l:ℂ) ∈ targetContact) (hr : (targetFrontParam r:ℂ) ∈ targetContact)
      (hgap : ∀ t : I, l < t → t < r → (targetFrontParam t:ℂ) ∉ targetContact) :
      (fun t : I ↦ (targetFrontParam t:ℂ)) '' Ioo l r =
        openSegment ℝ (targetFrontParam l:ℂ) (targetFrontParam r:ℂ) ∧
      openSegment ℝ (targetFrontParam l:ℂ) (targetFrontParam r:ℂ) ⊆ Metric.ball (0:ℂ) 1 ∧
      Disjoint (openSegment ℝ (targetFrontParam l:ℂ) (targetFrontParam r:ℂ)) circleK := by
    have hball : openSegment ℝ (targetFrontParam l:ℂ) (targetFrontParam r:ℂ) ⊆ Metric.ball (0:ℂ) 1 :=
      openSegment_subset_ball_of_ne
        (by simpa [Metric.mem_closedBall] using hTargetNorm _ (targetFrontParam l).property)
        (by simpa [Metric.mem_closedBall] using hTargetNorm _ (targetFrontParam r).property)
        (fun he ↦ hlr.ne (targetFrontParam.injective (Subtype.ext he)))
    refine ⟨hTargetGapGeometry l r hlr hl hr hgap,hball,disjoint_left.mpr ?_⟩
    rintro z hz ⟨w,rfl⟩
    have hn := hball hz
    simp [Metric.mem_ball] at hn
  obtain ⟨radialH,hRadialH⟩ := hRadialExtension (LF false ∪ LF true) ν hSourceCompact M N
    hSourceCenterAvoid hTargetCenterAvoid frontTargetMap
    (by intro z hz hn; exact hLiteralUniqueI z (hLiteralSweep.symm ▸ hz) hn)
    (by intro z hz hn; exact hγUnique z (hγClosure.symm ▸ hz) hn)
  have hRadialEndpoint (Q : ↥(LF false ∪ LF true)) :
      (radialH ⟨Q,⟨Q,Q.property,1,by simp,by simp⟩⟩:ℂ) = frontTargetMap Q := by
    simpa using hRadialH Q 1
  have hSourceSweepClosed : IsClosed (sweep M (LF false ∪ LF true)) := by
    rw [← hLiteralSweep]
    exact isClosed_closure
  have hTargetSweepClosed : IsClosed (sweep N ν) := by
    have he : closure γ = sweep N ν := hγClosure
    rw [← he]
    exact isClosed_closure
  have hSourceSweepContact : range σ ∩ sweep M (LF false ∪ LF true) =
      (LF false ∪ LF true) ∩ range σ := by
    rw [← hLiteralSweep]
    exact hSourceCurveMeet
  have hGluingAgree (x : ℂ) (hc : x ∈ range σ) (hs : x ∈ sweep M (LF false ∪ LF true)) :
      (hCircle ⟨x,hc⟩:ℂ) = radialH ⟨x,hs⟩ := by
    have hL := (show x ∈ (LF false ∪ LF true) ∩ range σ from hSourceSweepContact ▸ ⟨hc,hs⟩).1
    have hh := hRadialEndpoint ⟨x,hL⟩
    have he := hFrontTargetMap ⟨x,hL⟩
    exact (hSkeletonCurve ⟨x,hLX hL⟩ hc).symm.trans (he.symm.trans hh.symm)
  have hGluingOverlap (x : range σ) : (hCircle x:ℂ) ∈ sweep N ν ↔
      (x:ℂ) ∈ sweep M (LF false ∪ LF true) := by
    constructor
    · intro hx
      have hmem : (hCircle x:ℂ) ∈ targetContact := hTargetSweepContact ▸ ⟨(hCircle x).property,hx⟩
      obtain ⟨y,⟨z,hz,rfl⟩,he⟩ := hmem
      have hez : z = x := hCircle.injective (Subtype.ext he)
      have hL : (x:ℂ) ∈ LF false ∪ LF true := by simpa only [hez,mem_ofPred_eq] using hz
      exact ⟨x,hL,1,by simp,by simp⟩
    · intro hx
      have hL := (show (x:ℂ) ∈ (LF false ∪ LF true) ∩ range σ from
        hSourceSweepContact ▸ ⟨x.property,hx⟩).1
      have hc : (hCircle x:ℂ) ∈ targetContact :=
        ⟨hCircle x,⟨x,hL,rfl⟩,rfl⟩
      exact (show (hCircle x:ℂ) ∈ circleK ∩ sweep N ν from hTargetSweepContact.symm ▸ hc).2
  obtain ⟨wholeH,hWholeCurve,hWholeRadial⟩ := HolomorphicAnosov.closed_union_homeomorph_gluing
    (range σ) (sweep M (LF false ∪ LF true)) circleK (sweep N ν)
    hcCompact.isClosed hSourceSweepClosed (by
      have he : circleK = Metric.sphere (0:ℂ) 1 := by
        ext z
        exact ⟨fun ⟨w,hw⟩ ↦ hw ▸ w.property, fun hz ↦ ⟨⟨z,hz⟩,rfl⟩⟩
      rw [he]
      exact Metric.isClosed_sphere)
    hTargetSweepClosed hCircle radialH hGluingAgree hGluingOverlap
  let finalH : ↥(range σ ∪ closure (BS false ∪ BS true ∪ openSegment ℝ M (μ sP))) ≃ₜ
      ↥(circleK ∪ closure γ) :=
    (Homeomorph.setCongr (congrArg (fun S ↦ range σ ∪ S) hLiteralSweep)).trans
      (wholeH.trans (Homeomorph.setCongr (congrArg (fun S ↦ circleK ∪ S) hγClosure.symm)))
  have hFinalCurve (x : ↥(range σ ∪ closure (BS false ∪ BS true ∪ openSegment ℝ M (μ sP))))
      (hx : (x:ℂ) ∈ range σ) : (finalH x:ℂ) = h ⟨x,hx⟩ :=
    hWholeCurve ⟨x,(congrArg (fun S ↦ range σ ∪ S) hLiteralSweep) ▸ x.property⟩ hx
  have hFinalRadial (Q : ↥(LF false ∪ LF true)) (t : I)
      (x : ↥(range σ ∪ closure (BS false ∪ BS true ∪ openSegment ℝ M (μ sP))))
      (hx : (x:ℂ) = (1-(t:ℝ)) • M+(t:ℝ) • (Q:ℂ)) :
      (finalH x:ℂ) = (1-(t:ℝ)) • N+(t:ℝ) • (frontTargetMap Q:ℂ) := by
    have hxs : (x:ℂ) ∈ sweep M (LF false ∪ LF true) := ⟨Q,Q.property,t,t.property,hx⟩
    have hh := hWholeRadial
      ⟨x,(congrArg (fun S ↦ range σ ∪ S) hLiteralSweep) ▸ x.property⟩ hxs
    have he : (⟨(x:ℂ),hxs⟩ : sweep M (LF false ∪ LF true)) =
        ⟨(1-(t:ℝ)) • M+(t:ℝ) • (Q:ℂ),⟨Q,Q.property,t,t.property,rfl⟩⟩ := Subtype.ext hx
    exact hh.trans ((congrArg (fun z ↦ (radialH z:ℂ)) he).trans (hRadialH Q t))
  have hH₀Front (x : ↥(range σ ∪ segment ℝ (σ p) (σ q) ∪ (LF false ∪ LF true)))
      (hx : (x:ℂ) ∈ LF false ∪ LF true) : (H₀ x:ℂ) = frontTargetMap ⟨x,hx⟩ :=
    (hFrontTargetMap ⟨x,hx⟩).symm
  have hH₀Image : H₀ '' {x : ↥(range σ ∪ segment ℝ (σ p) (σ q) ∪ (LF false ∪ LF true)) | (x:ℂ) ∈ LF false ∪ LF true} = {y : ↥(circleK ∪ segment ℝ E₁ E₂ ∪ ν) | (y:ℂ) ∈ ν} := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      change (H₀ x:ℂ) ∈ ν
      rw [hH₀Front x hx]
      exact (frontTargetMap ⟨x,hx⟩).property
    · intro hy
      obtain ⟨Q,hQ⟩ := frontTargetMap.surjective ⟨y,hy⟩
      refine ⟨⟨Q,Or.inr Q.property⟩,Q.property,?_⟩
      apply Subtype.ext
      exact (hH₀Front _ Q.property).trans (congrArg Subtype.val hQ)
  have hH₀Curve (x : ↥(range σ ∪ segment ℝ (σ p) (σ q) ∪ (LF false ∪ LF true)))
      (hx : (x:ℂ) ∈ range σ) : (H₀ x:ℂ) = h ⟨x,hx⟩ :=
    hSkeletonCurve ⟨x,hSourceSkeletonSet.symm ▸ x.property⟩ hx
  have hH₀Affine (x₁ x₂ : range σ) (t : I)
      (x : ↥(range σ ∪ segment ℝ (σ p) (σ q) ∪ (LF false ∪ LF true)))
      (hgap : ((x₁:ℂ),(x₂:ℂ)) ∈ gapPairs (fun t : I ↦ (sourceFrontParam t:ℂ))
        ((LF false ∪ LF true) ∩ range σ))
      (hx : (x:ℂ) = (1-(t:ℝ)) • (x₁:ℂ)+(t:ℝ) • (x₂:ℂ)) :
      (H₀ x:ℂ) = (1-(t:ℝ)) • (h x₁:ℂ)+(t:ℝ) • (h x₂:ℂ) := by
    rw [← hSourceGapPairs] at hgap
    obtain ⟨u,v,huv,hu,hv,hfree,he⟩ := hgap
    let g : SourceGaps := ⟨(u,v),huv,hu,hv,hfree⟩
    have he1 : (x₁:ℂ) = μ u := congrArg Prod.fst he
    have he2 : (x₂:ℂ) = μ v := congrArg Prod.snd he
    have hh := hSkeletonAffine (some g) (t:ℝ) ⟨x,hSourceSkeletonSet.symm ▸ x.property⟩
      t.property (by change (x:ℂ) = (1-(t:ℝ)) • μ u+(t:ℝ) • μ v; rw [← he1,← he2]; exact hx)
    have hx1 : (⟨μ u,⟨α u,rfl⟩⟩ : range σ) = x₁ := Subtype.ext he1.symm
    have hx2 : (⟨μ v,⟨α v,rfl⟩⟩ : range σ) = x₂ := Subtype.ext he2.symm
    change (H₀ x:ℂ) = (1-(t:ℝ)) • (h ⟨μ u,⟨α u,rfl⟩⟩:ℂ)+(t:ℝ) • (h ⟨μ v,⟨α v,rfl⟩⟩:ℂ) at hh
    simpa only [hx1,hx2] using hh
  have hH₀Base (t : I)
      (x : ↥(range σ ∪ segment ℝ (σ p) (σ q) ∪ (LF false ∪ LF true)))
      (hx : (x:ℂ) = (1-(t:ℝ)) • σ p+(t:ℝ) • σ q) :
      (H₀ x:ℂ) = (1-(t:ℝ)) • E₁+(t:ℝ) • E₂ :=
    hSkeletonBase (t:ℝ) t.property ⟨x,by change (x:ℂ) ∈ range σ ∪ ⋃ i : Option SourceGaps, segment ℝ (σ (sourceLeft i)) (σ (sourceRight i)); rw [hSourceSkeletonSet]; exact x.property⟩ hx
  have hH₀Param (t : I)
      (x : ↥(range σ ∪ segment ℝ (σ p) (σ q) ∪ (LF false ∪ LF true)))
      (hx : (x:ℂ) = sourceFrontParam t) : (H₀ x:ℂ) = targetFrontParam t := by
    have hL : (x:ℂ) ∈ LF false ∪ LF true := hx.symm ▸ (sourceFrontParam t).property
    exact (hH₀Front x hL).trans
      (congrArg (fun Q ↦ (frontTargetMap Q:ℂ)) (Subtype.ext hx))
  -- Case-II provider instantiated with the actual half-sector geometry.
  -- Package the constructed source and target geometry in the literal statement.
  have hLF0 : halfFront ((σ p + σ q) / 2) (μ sP) (σ p)
      (range (μ.subpath 0 sP)) β = LF false := by
    simpa only [endpoint, M, Path.source] using (congrFun hLFFold false).symm
  have hLF1 : halfFront ((σ p + σ q) / 2) (μ sP) (σ q)
      (range (μ.subpath 1 sP)) β = LF true := by
    simpa only [endpoint, M, Path.target] using (congrFun hLFFold true).symm
  have hBS0 : halfStar ((σ p + σ q) / 2) (μ sP) (σ p)
      (range (μ.subpath 0 sP)) β = BS false := by
    simpa only [endpoint, M, Path.source] using (congrFun hBSFold false).symm
  have hBS1 : halfStar ((σ p + σ q) / 2) (μ sP) (σ q)
      (range (μ.subpath 1 sP)) β = BS true := by
    simpa only [endpoint, M, Path.target] using (congrFun hBSFold true).symm
  refine ⟨ε, τ, sP, hε, hτ, hs0, hs1, hP.symm, hray, ?_⟩
  have hLeftArc : (fun t : I ↦ σ (α t)) '' {t : I | t ≤ sP} =
      range (μ.subpath 0 sP) := by
    rw [Path.range_subpath_of_le μ 0 sP (by exact sP.property.1)]
    congr 1
    ext t
    simp only [mem_ofPred_eq, mem_Icc]
    exact ⟨fun ht ↦ ⟨t.property.1, ht⟩, And.right⟩
  have hRightArc : (fun t : I ↦ σ (α t)) '' {t : I | sP ≤ t} =
      range (μ.subpath 1 sP) := by
    rw [Path.range_subpath_of_ge μ 1 sP (by exact sP.property.2)]
    congr 1
    ext t
    simp only [mem_ofPred_eq, mem_Icc]
    exact ⟨fun ht ↦ ⟨ht, t.property.2⟩, And.left⟩
  have hPointLiteral : μ sP = (σ p + σ q) / 2 +
      τ • (ε • (Complex.I * (σ q - σ p))) := hμContact
  intro sourceLeftSet sourceRightSet literalL literalB literalC
  have hLiteralL : literalL = LF false ∪ LF true := by
    dsimp only [literalL, sourceLeftSet, sourceRightSet]
    rw [hLeftArc, hRightArc, ← hPointLiteral, hLF0, hLF1]
  have hLiteralB : literalB = BS false ∪ BS true ∪ openSegment ℝ M (μ sP) := by
    dsimp only [literalB, sourceLeftSet, sourceRightSet]
    rw [hLeftArc, hRightArc, ← hPointLiteral, hBS0, hBS1]
  have hLiteralC : literalC = (LF false ∪ LF true) ∩ range σ := by
    change literalL ∩ range σ = _
    rw [hLiteralL]
  rw [hLiteralC, hLiteralL, hLiteralB, ← hPointLiteral]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [M] using hSourceNonempty
  · simpa only [M] using hSourceOpen
  · simpa only [M] using hSourceSub
  · simpa only [M] using hSourceFront
  · simpa only [M] using hSourceCompact
  · refine ⟨?_, ?_⟩
    · simpa only [M] using hLiteralSweep
    · refine ⟨?_, ?_⟩
      · simpa only [M] using hLiteralOpenStar
      · refine ⟨?_, ?_⟩
        · intro z hz hzM
          apply hLiteralUniqueI z ?_ hzM
          simpa only [M] using hz
        · refine ⟨?_, ?_⟩
          · simpa only [M] using hSourceContactClosed
          · refine ⟨?_, ?_⟩
            · simpa only [M, hμrange] using hSourceContactSub
            · refine ⟨?_, ?_, ?_, ?_⟩
              · simpa only [M] using hSourceContactEndpoints.1
              · simpa only [M] using hSourceContactEndpoints.2.1
              · simpa only [M] using hSourceContactEndpoints.2.2
              · refine ⟨?_, ?_⟩
                · simpa only [M] using hSourceCurveMeet
                · refine ⟨sourceFrontParam, ?_, ?_, ?_⟩
                  · exact hSourceFrontParamEndpoints.1
                  · exact hSourceFrontParamEndpoints.2
                  · refine ⟨?_, ?_⟩
                    · intro u v s t hu hv hs ht
                      exact hFullFrontOrder s t u v hs ht
                    · refine ⟨?_, ?_⟩
                      · change gapPairs μ _ = _
                        exact hSourceGapPairs
                      · refine ⟨?_, ?_, ?_, ?_, ?_⟩
                        · intro l r hlr hl hr hgap
                          simpa only [M, Ioo] using hSourceGapGeometry l r hlr
                            (by simpa only [M] using hl)
                            (by simpa only [M] using hr)
                            (by simpa only [M] using hgap)
                        · intro x hx
                          have hraw := HolomorphicAnosov.embedded_interval_contact_gap μ
                            (hσ.comp hα) ((LF false ∪ LF true) ∩ range σ)
                            hSourceContactClosed
                            (by simpa using hSourceContactEndpoints.1)
                            (by simpa using hSourceContactEndpoints.2.1) x
                            (by simpa only [M, hμrange] using hx)
                          simpa only [hμEval, hμrange, Ioo, Set.mem_ofPred_eq] using hraw
                        · intro x hx
                          have hraw := HolomorphicAnosov.embedded_interval_contact_gap
                            (fun t : I ↦ (sourceFrontParam t : ℂ)) hSourceFrontEmbedding
                            ((LF false ∪ LF true) ∩ range σ) hSourceContactClosed
                            (by simpa only [hSourceFrontParamEndpoints.1] using hSourceContactEndpoints.1)
                            (by simpa only [hSourceFrontParamEndpoints.2] using hSourceContactEndpoints.2.1) x
                            (by simpa [hSourceFrontRange, M] using hx)
                          rw [hSourceFrontRange] at hraw
                          exact hraw
                        · have hraw := HolomorphicAnosov.embedded_interval_contact_components_countable
                            (fun t : I ↦ (sourceFrontParam t : ℂ)) hSourceFrontEmbedding
                            ((LF false ∪ LF true) ∩ range σ) hSourceContactClosed
                            (by simpa only [hSourceFrontParamEndpoints.1] using hSourceContactEndpoints.1)
                            (by simpa only [hSourceFrontParamEndpoints.2] using hSourceContactEndpoints.2.1)
                          simpa only [hSourceFrontRange, Ioo, Set.mem_ofPred_eq] using hraw
                        · obtain ⟨ds, hds, hdc, hdp⟩ := hSourceDirectionData
                          refine ⟨ds, ?_, ?_, ?_, ?_⟩
                          · simpa only [M] using hds
                          · simpa only [M] using hdc
                          · simpa only [M] using hdp
                          · refine ⟨ν,H₀,?_,?_,?_,?_,?_⟩
                            · rw [hH₀Image]
                              ext z
                              exact ⟨fun ⟨y,hy,he⟩ ↦ he ▸ hy,
                                fun hz ↦ ⟨⟨z,Or.inr hz⟩,hz,rfl⟩⟩
                            · exact hH₀Curve
                            · exact hH₀Affine
                            · exact hH₀Base
                            · have hContactLiteral : targetContact =
                                  Subtype.val '' h '' {x : range σ | (x:ℂ) ∈ (LF false ∪ LF true) ∩ range σ} := by
                                ext z
                                constructor
                                · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
                                  exact ⟨h x,⟨x,⟨hx,x.property⟩,rfl⟩,rfl⟩
                                · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
                                  exact ⟨hCircle x,⟨x,hx.1,rfl⟩,rfl⟩
                              refine ⟨hνCompact,?_,hγNonempty,hγOpen,hγFrontier,hγClosure,
                                hγBallSide,hγUnique,targetFrontParam,hTargetFrontEndpoints.1,
                                hTargetFrontEndpoints.2,?_,?_,?_,dt,hdt,hdtContinuous,hdtPositive,
                                finalH,hFinalCurve,?_⟩
                              · exact hνContact.trans hContactLiteral
                              · exact hH₀Param
                              · simpa only [hContactLiteral] using hTargetGapPairs
                              · simpa only [hContactLiteral,Ioo] using hTargetGapGeometryFull
                              · intro Q t x y hy hx
                                have hQ : (y:ℂ) ∈ LF false ∪ LF true := hy.symm ▸ Q.property
                                have he : (H₀ y:ℂ) = frontTargetMap ⟨Q,Q.property⟩ :=
                                  (hH₀Front y hQ).trans (congrArg (fun R ↦ (frontTargetMap R:ℂ)) (Subtype.ext hy))
                                rw [he]
                                exact hFinalRadial ⟨Q,Q.property⟩ t x hx



end HolomorphicAnosov.Topology.Plane

