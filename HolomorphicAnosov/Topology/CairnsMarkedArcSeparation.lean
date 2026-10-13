import HolomorphicAnosov.Topology.CairnsContinuousPolygonCrossing
import HolomorphicAnosov.Topology.CairnsMarkedSegmentPolygonClosure

/-! DAG node: `topo.cairns_marked_arc_separation_g10`. -/

open Set Metric
namespace HolomorphicAnosov

/-- A straight segment meeting a simple polygon once, in the interior of both
segments, is a transverse crossing. Cairns (1951), Theorem 2.1, p.860.
The signed distance to the edge line is affine in the path parameter and vanishes
at the crossing. Its slope cannot vanish: the local-line description would then
put a second nearby point of the straight segment on the polygon. Thus the affine
function has strictly opposite signs before and after the crossing. -/
theorem cairns_straight_segment_crossing {n : ℕ} (P : Polygon ℂ (n + 1))
    (hP : IsSimpleClosedPolygon P) {a b m : ℂ} (hab : a ≠ b)
    (hm : m ∈ openSegment ℝ a b)
    (hinter : segment ℝ a b ∩ P.boundary ℝ = {m})
    (i : Fin (n + 1)) (hedge : m ∈ openSegment ℝ (P i) (P (finRotate (n+1) i))) :
    CrossesPolygonOnce P (AffineMap.lineMap a b (k := ℝ)) := by
  let f := AffineMap.lineMap a b (k := ℝ)
  have hf : Continuous f := by fun_prop
  have hinj : Function.Injective f := AffineMap.lineMap_injective ℝ hab
  obtain ⟨t, ht, htm⟩ := (openSegment_eq_image_lineMap ℝ a b ▸ hm)
  change f t = m at htm
  let v := P (finRotate (n+1) i) - P i
  let F : ℂ → ℝ := fun z ↦ (star v * (z - P i)).im
  let slope : ℝ := (star v * (b - a)).im
  have hFaff (s : ℝ) : F (f s) = s * slope + F a := by
    simp only [F, f, slope, AffineMap.lineMap_apply_module', Complex.real_smul,
      mul_add, mul_sub, Complex.add_im, Complex.sub_im, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    ring
  obtain ⟨ε, hε, hline⟩ := polygon_edge_local_line P hP.2.2.1 hP.2.2.2 i hedge
  have hFm : F m = 0 := (hline m (mem_ball_self hε)).mp
    (hinter.symm ▸ (show m ∈ ({m} : Set ℂ) from rfl)).2
  have hFt : t * slope + F a = 0 := by rw [← hFaff, htm]; exact hFm
  have hslope : slope ≠ 0 := by
    intro hz
    have hnear : Ioo (0 : ℝ) 1 ∩ f ⁻¹' ball m ε ∈ nhds t :=
      ((isOpen_Ioo.inter (isOpen_ball.preimage hf)).mem_nhds
        ⟨ht, by simpa only [mem_preimage, htm] using mem_ball_self hε⟩)
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
    have hclose : t + δ / 2 ∈ ball t δ := by
      rw [mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
      exact half_lt_self hδ
    have hs := hδsub hclose
    have hFs : F (f (t + δ / 2)) = 0 := by rw [hFaff, hz, mul_zero, zero_add]; simpa [hz] using hFt
    have hpoly := (hline _ hs.2).mpr hFs
    have hseg : f (t + δ / 2) ∈ segment ℝ a b :=
      openSegment_subset_segment ℝ _ _ (lineMap_mem_openSegment ℝ _ _ hs.1)
    have heq : f (t + δ / 2) = m := hinter.subset ⟨hseg, hpoly⟩
    have := hinj (heq.trans htm.symm)
    linarith
  refine ⟨i, t, ht, ?_, htm.symm ▸ hedge, min t (1-t) / 2, ?_, ?_, ?_, ?_⟩
  · change f '' Icc 0 1 ∩ P.boundary ℝ = {f t}
    rw [htm]
    exact (show f '' Icc 0 1 = segment ℝ a b from (segment_eq_image_lineMap ℝ a b).symm) ▸ hinter
  · exact half_pos (lt_min ht.1 (sub_pos.mpr ht.2))
  · have : min t (1-t) ≤ t := min_le_left _ _
    have : 0 < min t (1-t) := lt_min ht.1 (sub_pos.mpr ht.2)
    linarith
  · have : min t (1-t) ≤ 1-t := min_le_right _ _
    have : 0 < min t (1-t) := lt_min ht.1 (sub_pos.mpr ht.2)
    linarith
  · intro s hs u hu
    change F (f s) * F (f u) < 0
    have hform (r : ℝ) : F (f r) = (r-t) * slope := by rw [hFaff]; nlinarith [hFt]
    rw [hform, hform]
    have hmul : (s-t)*(u-t) < 0 := mul_neg_of_neg_of_pos (sub_neg.mpr hs.2) (sub_pos.mpr hu.1)
    have hsquare : 0 < slope * slope := mul_self_pos.mpr hslope
    nlinarith [mul_neg_of_neg_of_pos hmul hsquare]

/-- A compact obstacle containing a continuous arc between the endpoints of a
chord prevents reconnection of a transverse stub around that chord.
Cairns (1951), Lemma 3.1(A,C), pp.861–862. If the stub endpoints could reconnect,
the marked closure theorem would produce a polygon missing the obstacle and
crossing the chord once. The polygon theorem puts the chord endpoints in distinct
components of its complement, while the arc in the obstacle connects them there.
This contradiction proves the asserted separation. -/
theorem cairns_marked_arc_separation
    (K : Set ℂ) (hK : IsCompact K) (a b m xminus xplus : ℂ)
    (hab : a ≠ b) (hm : m ∈ openSegment ℝ a b)
    (hx : xminus ≠ xplus)
    (hstub : Disjoint (segment ℝ xminus xplus) K)
    (hinter : segment ℝ xminus xplus ∩ segment ℝ a b = {m})
    (hmstub : m ∈ openSegment ℝ xminus xplus)
    (hnonparallel : ¬ ∃ t : ℝ, xplus - xminus = t • (b-a))
    (γ : unitInterval → ℂ) (hγ : Continuous γ)
    (hγ0 : γ 0 = a) (hγ1 : γ 1 = b) (hγK : range γ ⊆ K) :
    xplus ∉ connectedComponentIn (K ∪ segment ℝ a b)ᶜ xminus := by
  intro hconnect
  obtain ⟨n, P, hPinj, hPnd, hPinter, hPK, hPd, i, hmi, hline⟩ :=
    cairns_marked_segment_polygon_closure K hK a b m xminus xplus hab hm hx
      hstub hinter hmstub hnonparallel hconnect
  have hP : IsSimpleClosedPolygon P := by
    refine ⟨by omega, hPinj, hPnd, ?_⟩
    intro j k hjk
    rw [hPinter j k hjk, image_inter hPinj]
    simp only [image_pair]
    exact subset_rfl
  have hc := cairns_straight_segment_crossing P hP hab hm
    (by rw [inter_comm]; exact hPd) i hmi
  have hsep := cairns_continuous_polygon_crossing P hP
    (AffineMap.lineMap a b (k := ℝ)) (by fun_prop)
    (AffineMap.lineMap_injective ℝ hab).injOn hc
  simp only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at hsep
  have hγpoly : range γ ⊆ (P.boundary ℝ)ᶜ := by
    intro z hz hzb
    exact disjoint_left.mp hPK hzb (hγK hz)
  have hγconn : IsPreconnected (range γ) :=
    isPreconnected_range hγ
  have hcomp : b ∈ connectedComponentIn (P.boundary ℝ)ᶜ a :=
    hγconn.subset_connectedComponentIn ⟨0, hγ0⟩ hγpoly ⟨1, hγ1⟩
  exact hsep (connectedComponentIn_eq hcomp)

end HolomorphicAnosov

