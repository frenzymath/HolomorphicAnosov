import HolomorphicAnosov.Topology.SegmentChainPolygonClosure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.IntermediateValue

/-!
# A simple polygon with two protected radial circle crossings

DAG node: `topo.cairns_round_disk_two_walk_polygon_assembly_residual_g7`.
Source: Cairns (1951), Lemma 5.1, p.866. The finite assembly omitted in
that paragraph is proved by a shortest connector and local radial clearance.
-/

namespace HolomorphicAnosov
open Set Filter Topology _root_.Topology

/-- Source: scalar interval geometry in Cairns (1951), Lemma 5.1, p.866.
Real radial segments are the images of their scalar intervals. -/
theorem radial_segment_mem_iff {z y : ℂ} {l h : ℝ} (hlh : l ≤ h) :
    y ∈ segment ℝ (l • z) (h • z) ↔ ∃ t ∈ Icc l h, t • z = y := by
  let L : ℝ →ₗ[ℝ] ℂ := LinearMap.toSpanSingleton ℝ ℂ z
  have he := image_segment ℝ L.toAffineMap l h
  rw [segment_eq_Icc hlh] at he
  exact he ▸ Iff.rfl

/-- Source: scalar interval geometry in Cairns (1951), Lemma 5.1, p.866.
The norm identifies the scalar on a positive unit radial interval. -/
theorem radial_segment_norm {z y : ℂ} {l h : ℝ} (hz : ‖z‖ = 1)
    (hl : 0 ≤ l) (hlh : l ≤ h) (hy : y ∈ segment ℝ (l • z) (h • z)) :
    ∃ t ∈ Icc l h, y = t • z ∧ ‖y‖ = t := by
  obtain ⟨t, ht, rfl⟩ := (radial_segment_mem_iff hlh).mp hy
  refine ⟨t, ht, rfl, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hl.trans ht.1), hz, mul_one]

/-- Source: radial clearance in Cairns (1951), Lemma 5.1, p.866.
Distinct unit radial rays have disjoint positive compact intervals. -/
theorem positive_radial_segments_disjoint {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : a ≠ b) {l h m k : ℝ} (hl : 0 < l) (hm : 0 < m)
    (hlh : l ≤ h) (hmk : m ≤ k) :
    Disjoint (segment ℝ (l • a) (h • a)) (segment ℝ (m • b) (k • b)) := by
  apply Set.disjoint_left.mpr
  intro z hza hzb
  obtain ⟨s, hs, hzs, hns⟩ := radial_segment_norm ha hl.le hlh hza
  obtain ⟨t, ht, hzt, hnt⟩ := radial_segment_norm hb hm.le hmk hzb
  have hst : s = t := hns.symm.trans hnt
  have he : s • a = s • b := by rw [← hzs, hst, ← hzt]
  exact hab ((smul_right_injective ℂ (ne_of_gt (hl.trans_le hs.1))) he)

/-- Source: local straight-edge geometry in Cairns (1951), Lemma 5.1, p.866.
A segment that is locally contained in a vector subspace near one of its
points has both endpoints in that subspace, provided the point is in it.
Use a small positive affine parameter toward each endpoint and divide its
nonzero coefficient in the subspace. -/
theorem segment_endpoints_mem_of_local_submodule
    (L : Submodule ℝ ℂ) {x y b : ℂ} (hb : b ∈ segment ℝ x y) (hbL : b ∈ L)
    {δ : ℝ} (hδ : 0 < δ)
    (hlocal : ∀ z ∈ segment ℝ x y, z ∈ Metric.ball b δ → z ∈ L) :
    x ∈ L ∧ y ∈ L := by
  have hend (a : ℂ) (ha : a ∈ segment ℝ x y) : a ∈ L := by
    let f : ℝ → ℂ := fun t ↦ (1-t) • b + t • a
    have hf : Continuous f := by fun_prop
    have hf0 : f 0 = b := by simp [f]
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp
      (hf.continuousAt.preimage_mem_nhds (hf0.symm ▸ Metric.ball_mem_nhds b hδ))
    let t := min ε 1 / 2
    have ht : 0 < t := half_pos (lt_min hε zero_lt_one)
    have htε : t < ε := (half_lt_self (lt_min hε zero_lt_one)).trans_le (min_le_left _ _)
    have ht1 : t < 1 := (half_lt_self (lt_min hε zero_lt_one)).trans_le (min_le_right _ _)
    have htb : t ∈ Metric.ball (0 : ℝ) ε := by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using htε
    have hft : f t ∈ segment ℝ x y :=
      (convex_segment x y) hb ha (by linarith) ht.le (by ring)
    have hL := L.sub_mem (hlocal (f t) hft (by simpa only [Set.mem_preimage, hf0] using hεs htb)) (L.smul_mem (1-t) hbL)
    have hsm : t • a ∈ L := by simpa [f] using hL
    exact (L.smul_mem_iff ht.ne').mp hsm
  exact ⟨hend x (left_mem_segment ℝ x y), hend y (right_mem_segment ℝ x y)⟩

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set
/-- Source: collinear shortcut in Cairns (1951), Lemma 5.1, p.866.
Three collinear points give a shortcut through their two joining segments. -/
theorem segment_subset_two_of_collinear {x b y : ℂ} (hxy : x ≠ y)
    (hc : Collinear ℝ ({x,b,y} : Set ℂ)) :
    segment ℝ x y ⊆ segment ℝ x b ∪ segment ℝ b y := by
  have hb : b ∈ Set.range (AffineMap.lineMap x y : ℝ → ℂ) :=
    mem_affineSpan_pair_iff_exists_lineMap_eq.mp
      (hc.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hxy)
  intro z hz
  rw [← insert_endpoints_openSegment] at hz
  rcases hz with rfl | rfl | hz
  · exact Or.inl (left_mem_segment ℝ _ _)
  · exact Or.inr (right_mem_segment ℝ _ _)
  · rcases openSegment_subset_union x y hb hz with rfl | hz | hz
    · exact Or.inl (right_mem_segment ℝ _ _)
    · exact Or.inl (openSegment_subset_segment ℝ _ _ hz)
    · exact Or.inr (openSegment_subset_segment ℝ _ _ hz)

/-- Source: agent-written finite assembly detail of Cairns (1951), Lemma 5.1, p.866.
A shortest connector crossing a locally radial portion of X crosses it in
an edge interior. A marked vertex would have two radial incident edges and
therefore admit a direct shortcut, contradicting minimality. -/
theorem polygon_shortest_radial_contact
    {n : ℕ} (p : Polygon ℂ (n+3)) (X : Set ℂ) (b : ℂ)
    (hinj : Function.Injective p.vertices)
    (hothers : ∀ i : Fin (n+3), i ≠ Fin.last (n+2) → p.edgeSet ℝ i ⊆ X)
    (hshort : ∀ i j : Fin (n+3), i.val + 2 = j.val → ¬segment ℝ (p i) (p j) ⊆ X)
    (hb0 : b ≠ p 0) (hbL : b ≠ p (Fin.last (n+2)))
    (hlocal : ∃ δ > 0, ∀ z ∈ X, z ∈ Metric.ball b δ → z ∈ Submodule.span ℝ {b})
    (hcross : ∃ i : Fin (n+3), i ≠ Fin.last (n+2) ∧ b ∈ p.edgeSet ℝ i) :
    ∃ (i : Fin (n+3)) (r s : ℝ), p i = r • b ∧
      p (finRotate (n+3) i) = s • b ∧ b ∈ openSegment ℝ (p i) (p (finRotate (n+3) i)) := by
  obtain ⟨δ,hδ,hδs⟩ := hlocal
  have hend (i : Fin (n+3)) (hi : i ≠ Fin.last (n+2)) (hb : b ∈ p.edgeSet ℝ i) :
      p i ∈ Submodule.span ℝ {b} ∧ p (finRotate (n+3) i) ∈ Submodule.span ℝ {b} := by
    apply segment_endpoints_mem_of_local_submodule (Submodule.span ℝ {b})
      (by simpa [Polygon.edgeSet, affineSegment_eq_segment] using hb)
      (Submodule.mem_span_singleton_self b) hδ
    intro z hz hzb
    exact hδs z (hothers i hi (by simpa [Polygon.edgeSet, affineSegment_eq_segment] using hz)) hzb
  have hnvertex : ∀ k : Fin (n+3), b ≠ p k := by
    intro k heq
    have hk0 : 0 < k.val := by
      by_contra h
      have hk : k = 0 := Fin.ext (by change k.val = 0; omega)
      exact hb0 (hk ▸ heq)
    have hkL : k.val < n+2 := by
      by_contra h
      have hk : k = Fin.last (n+2) := Fin.ext (by have := k.isLt; simp; omega)
      exact hbL (hk ▸ heq)
    let i : Fin (n+3) := ⟨k.val-1, by omega⟩
    let j : Fin (n+3) := ⟨k.val+1, by omega⟩
    have hi : i ≠ Fin.last (n+2) := by intro h; have := congrArg Fin.val h; dsimp [i] at this; simp at this; omega
    have hk : k ≠ Fin.last (n+2) := by intro h; have := congrArg Fin.val h; simp at this; omega
    have hik : finRotate (n+3) i = k := by apply Fin.ext; rw [coe_finRotate_of_ne_last hi]; dsimp [i]; omega
    have hkj : finRotate (n+3) k = j := by apply Fin.ext; rw [coe_finRotate_of_ne_last hk]
    have hiB : b ∈ p.edgeSet ℝ i := by
      rw [Polygon.edgeSet, affineSegment_eq_segment, hik, heq]
      exact right_mem_segment ℝ _ _
    have hkB : b ∈ p.edgeSet ℝ k := by
      rw [Polygon.edgeSet, affineSegment_eq_segment, heq]
      exact left_mem_segment ℝ _ _
    have hiL := (hend i hi hiB).1
    have hjL : p j ∈ Submodule.span ℝ {b} := hkj ▸ (hend k hk hkB).2
    have hcol : Collinear ℝ ({p i,b,p j} : Set ℂ) := by
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      refine ⟨0,b,?_⟩
      intro z hz
      have hzL : z ∈ Submodule.span ℝ {b} := by
        rcases hz with hz | hz | hz
        · exact hz ▸ hiL
        · simpa only [hz] using (Submodule.mem_span_singleton_self b (R := ℝ))
        · exact hz ▸ hjL
      obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hzL
      exact ⟨r,by simpa using hr.symm⟩
    have hij : i.val+2 = j.val := by dsimp [i,j]; omega
    apply hshort i j hij
    have hne : p i ≠ p j := fun h ↦ by have := congrArg Fin.val (hinj h); omega
    apply (segment_subset_two_of_collinear hne hcol).trans
    apply union_subset
    · simpa only [Polygon.edgeSet, affineSegment_eq_segment, hik, ← heq] using hothers i hi
    · simpa only [Polygon.edgeSet, affineSegment_eq_segment, hkj, ← heq] using hothers k hk
  obtain ⟨i,hi,hbi⟩ := hcross
  obtain ⟨hr,hs⟩ := hend i hi hbi
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hr
  obtain ⟨s,hs⟩ := Submodule.mem_span_singleton.mp hs
  exact ⟨i,r,s,hr.symm,hs.symm,mem_openSegment_of_ne_left_right (hnvertex i).symm
    (hnvertex _).symm (by simpa [Polygon.edgeSet, affineSegment_eq_segment] using hbi)⟩

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set
/-- Source: intermediate-value step of Cairns (1951), Lemma 5.1, p.866.
A finite connector from inside to outside a circle has an edge meeting it.
This is the intermediate value theorem on the first edge whose endpoint is
outside; induction only concerns the ordered connector, not its closing edge. -/
theorem polygon_connector_meets_unit_sphere {n : ℕ} (p : Polygon ℂ (n+3))
    (hfirst : ‖p 0‖ < 1) (hlast : 1 < ‖p (Fin.last (n+2))‖) :
    ∃ (i : Fin (n+3)) (z : ℂ), i ≠ Fin.last (n+2) ∧
      z ∈ p.edgeSet ℝ i ∧ ‖z‖ = 1 := by
  by_contra hn
  have hall : ∀ k : ℕ, (hk : k < n+3) → ‖p ⟨k,hk⟩‖ < 1 := by
    intro k
    induction k with
    | zero => intro hk; simpa using hfirst
    | succ k ih =>
      intro hk
      have hk' : k < n+3 := by omega
      have hp := ih hk'
      by_contra hnot
      have hle : 1 ≤ ‖p ⟨k+1,hk⟩‖ := le_of_not_gt hnot
      obtain ⟨z,hz,hzn⟩ := (convex_segment (p ⟨k,hk'⟩) (p ⟨k+1,hk⟩)).isPreconnected.intermediate_value
        (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
        continuous_norm.continuousOn (show (1 : ℝ) ∈ Icc ‖p ⟨k,hk'⟩‖ ‖p ⟨k+1,hk⟩‖ from ⟨hp.le,hle⟩)
      apply hn
      have hi : (⟨k,hk'⟩ : Fin (n+3)) ≠ Fin.last (n+2) := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      refine ⟨⟨k,hk'⟩,z,hi,?_,hzn⟩
      simpa only [Polygon.edgeSet, affineSegment_eq_segment, show finRotate (n+3) ⟨k,hk'⟩ = ⟨k+1,hk⟩ from
        Fin.ext (coe_finRotate_of_ne_last hi)] using hz
  have h := hall (n+2) (by omega)
  exact (not_lt_of_gt hlast) h
end HolomorphicAnosov
open Set

namespace HolomorphicAnosov

/-- A finite simple polygon avoiding K with two radial unit-circle crossings.
Source: Cairns (1951), Lemma 5.1, p.866. -/
def CairnsTwoWalkPolygonCertificate (K : Set ℂ) (a b : ℂ) : Prop :=
  ∃ (n : ℕ) (P : Polygon ℂ n),
    3 ≤ n ∧ Function.Injective P.vertices ∧ P.HasNondegenerateEdges ∧
    (∀ i j : Fin n, i ≠ j →
      P.edgeSet ℝ i ∩ P.edgeSet ℝ j =
        ({P i, P (finRotate n i)} ∩ {P j, P (finRotate n j)})) ∧
    Disjoint (P.boundary ℝ) K ∧
    P.boundary ℝ ∩ Metric.sphere (0 : ℂ) 1 = {a, b} ∧
    (∀ z ∈ ({a, b} : Set ℂ), ∃ (i : Fin n) (r s : ℝ),
      P i = r • z ∧ P (finRotate n i) = s • z ∧
      z ∈ openSegment ℝ (P i) (P (finRotate n i)))

/-- Source: Cairns (1951), Lemma 5.1, polygonal completion paragraph, p.866.
This is the agent-written finite construction omitted in that paragraph.

Choose a short protected radial segment through a and remove its interior
from the connector carrier X. Include in X the inner finite segment union,
the exterior of the radius-two closed ball, both remaining a-ray tails, and
the full b-ray segment from its inner collar endpoint to 4b. Scalar interval
coordinates show X meets the removed segment only at its two endpoints; the
inner union misses it by protection, the exterior by its norm bound, and the
b-ray by distinct positive unit directions. Following the inner chain, b-ray,
reversed exterior chain and a-ray tails gives a finite connector in X.

The shared shortest-segment-chain theorem closes a shortest connector by the
removed segment. Shortcuts exclude all improper edge intersections and any
shortcut across two consecutive connector edges. The resulting simple polygon
misses K by the given collar and exterior avoidance. Its closing edge meets
the unit circle exactly at a; X meets that circle only at b. Its connector
starts inside and ends outside the circle, so the intermediate value theorem
places b on a connector edge.

Near b, X lies in the real line spanned by b: the finite inner union has the
given clearance, the distant exterior misses a half-radius ball, and the
compact a-ray has positive distance from b. A segment through b locally in
that line has both endpoints in it, by taking a small positive affine step
toward each endpoint. If b were a connector vertex, its two incident edges
would therefore be collinear, and the segment between their other endpoints
would lie in their union, contradicting minimality. Thus b is in an edge
interior, whose endpoints are real multiples of b. The closing edge already
has the corresponding property at a. This proves every certificate conjunct
without changing the original hypotheses, parameter points, or obstacle.
-/
theorem cairns_round_disk_two_walk_polygon_assembly_residual
    (K : Set ℂ) (_hK : IsCompact K)
    (hKdisk : K ⊆ Metric.closedBall (0 : ℂ) 1)
    (u v a b : ℂ) (_hu : u ∈ Metric.sphere (0 : ℂ) 1)
    (_hv : v ∈ Metric.sphere (0 : ℂ) 1) (_huv : u ≠ v)
    (_hKcircle : K ∩ Metric.sphere (0 : ℂ) 1 = {u, v})
    (ha : a ∈ Metric.sphere (0 : ℂ) 1 \ {u, v})
    (hb : b ∈ Metric.sphere (0 : ℂ) 1 \ {u, v})
    (harcs : b ∉ connectedComponentIn (Metric.sphere (0 : ℂ) 1 \ {u, v}) a)
    (eta_a eta_b : ℝ) (heta_a : 0 < eta_a ∧ eta_a < 1)
    (heta_b : 0 < eta_b ∧ eta_b < 1)
    (hcollar_a : Disjoint (segment ℝ a ((1 - eta_a) • a)) K)
    (hcollar_b : Disjoint (segment ℝ b ((1 - eta_b) • b)) K)
    (hcomponent : (1 - eta_b) • b ∈
      connectedComponentIn (Metric.ball (0 : ℂ) 1 \ K) ((1 - eta_a) • a))
    (S : Finset (ℂ × ℂ))
    (hSwalk : Relation.ReflTransGen (fun p q ↦ (p, q) ∈ S)
      ((1 - eta_a) • a) ((1 - eta_b) • b))
    (hSdisk : (⋃ q ∈ S, segment ℝ q.1 q.2) ⊆
      Metric.ball (0 : ℂ) 1 \ K)
    (_hScompact : IsCompact (⋃ q ∈ S, segment ℝ q.1 q.2))
    (hclearance : ∀ z ∈ ({a, b} : Set ℂ), ∃ δ : ℝ,
      0 < δ ∧ Metric.closedBall z δ ⊆
        (⋃ q ∈ S, segment ℝ q.1 q.2)ᶜ)
    (hexterior_far : Relation.ReflTransGen
      (fun p q : ℂ ↦ segment ℝ p q ⊆ (Metric.closedBall (0 : ℂ) 2)ᶜ)
      ((4 : ℝ) • a) ((4 : ℝ) • b))
    (houteravoid : ∀ z ∈ ({a, b} : Set ℂ),
      Disjoint (segment ℝ z ((4 : ℝ) • z)) K)
    (hprotected_crossing : ∀ z ∈ ({a, b} : Set ℂ), ∃ ε : ℝ,
      0 < ε ∧ ε < eta_a ∧ ε < eta_b ∧ ε < 1 / 2 ∧
      z ∈ openSegment ℝ ((1 - ε) • z) ((1 + ε) • z) ∧
      Disjoint (segment ℝ ((1 - ε) • z) ((1 + ε) • z))
        (⋃ q ∈ S, segment ℝ q.1 q.2) ∧
      ∀ p q : ℂ, segment ℝ p q ⊆ (Metric.closedBall (0 : ℂ) 2)ᶜ →
        Disjoint (segment ℝ ((1 - ε) • z) ((1 + ε) • z)) (segment ℝ p q)) :
    CairnsTwoWalkPolygonCertificate K a b := by
  classical
  have han : ‖a‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using ha.1
  have hbn : ‖b‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hb.1
  have hab : a ≠ b := by intro h; subst b; exact harcs (mem_connectedComponentIn ha)
  obtain ⟨ε,hε,hεa,hεb,hεhalf,hacross,hacentral,_⟩ := hprotected_crossing a (by simp)
  let va := (1-ε) • a
  let wa := (1+ε) • a
  let ai := (1-eta_a) • a
  let bi := (1-eta_b) • b
  let Q := ⋃ q ∈ S, segment ℝ q.1 q.2
  let R := segment ℝ bi ((4 : ℝ) • b)
  let A₀ := segment ℝ ai va
  let A₁ := segment ℝ wa ((4 : ℝ) • a)
  let X := Q ∪ (Metric.closedBall (0 : ℂ) 2)ᶜ ∪ A₀ ∪ A₁ ∪ R
  have hε1 : ε < 1 := by linarith
  have hε4 : 1+ε < 4 := by linarith
  have hai : 0 < 1-eta_a := sub_pos.mpr heta_a.2
  have hbi : 0 < 1-eta_b := sub_pos.mpr heta_b.2
  have hva : 0 < 1-ε := sub_pos.mpr hε1
  have hwa : 0 < 1+ε := by linarith
  have hcentral_norm (z : ℂ) (hz : z ∈ segment ℝ va wa) : ‖z‖ ≤ 1+ε := by
    obtain ⟨t,ht,_,hn⟩ := radial_segment_norm han hva.le (by linarith : 1-ε ≤ 1+ε) hz
    exact hn ▸ ht.2
  have hcentral_b : Disjoint (segment ℝ va wa) R :=
    positive_radial_segments_disjoint han hbn hab hva hbi (by linarith) (by linarith [heta_b.1])
  have hcentral_A₀ : ∀ z ∈ A₀, z ∈ segment ℝ va wa → z = va := by
    intro z hz hzc
    obtain ⟨s,hs,hzs,_⟩ := radial_segment_norm han hai.le (by linarith : 1-eta_a ≤ 1-ε) hz
    obtain ⟨t,ht,hzt,_⟩ := radial_segment_norm han hva.le (by linarith : 1-ε ≤ 1+ε) hzc
    have han0 : a ≠ 0 := by intro h; simp [h] at han
    have hst : s = t := (smul_left_injective ℝ han0) (hzs.symm.trans hzt)
    have hsval : s = 1-ε := by linarith [hs.2,ht.1]
    simpa only [va,hsval] using hzs
  have hcentral_A₁ : ∀ z ∈ A₁, z ∈ segment ℝ va wa → z = wa := by
    intro z hz hzc
    obtain ⟨s,hs,hzs,_⟩ := radial_segment_norm han hwa.le hε4.le hz
    obtain ⟨t,ht,hzt,_⟩ := radial_segment_norm han hva.le (by linarith : 1-ε ≤ 1+ε) hzc
    have han0 : a ≠ 0 := by intro h; simp [h] at han
    have hst : s = t := (smul_left_injective ℝ han0) (hzs.symm.trans hzt)
    have hsval : s = 1+ε := by linarith [hs.1,ht.2]
    simpa only [wa,hsval] using hzs
  have hXcentral : ∀ z ∈ X, z ∈ segment ℝ va wa → z = va ∨ z = wa := by
    intro z hz hzc
    rcases hz with (((hz | hz) | hz) | hz) | hz
    · exact (Set.disjoint_left.mp hacentral hzc hz).elim
    · have hzn : 2 < ‖z‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
      have := hcentral_norm z hzc
      linarith
    · exact Or.inl (hcentral_A₀ z hz hzc)
    · exact Or.inr (hcentral_A₁ z hz hzc)
    · exact (Set.disjoint_left.mp hcentral_b hzc hz).elim
  have hva_ne : va ≠ wa := by
    intro h
    have han0 : a ≠ 0 := by intro h; simp [h] at han
    have := (smul_left_injective ℝ han0) h
    linarith
  have ha_va : a ≠ va := by
    intro h
    have hnorm := congrArg norm h
    simp only [va,norm_smul,Real.norm_eq_abs,abs_of_pos hva,han,mul_one] at hnorm
    linarith
  have ha_wa : a ≠ wa := by
    intro h
    have hnorm := congrArg norm h
    simp only [wa,norm_smul,Real.norm_eq_abs,abs_of_pos hwa,han,mul_one] at hnorm
    linarith
  have haX : a ∉ X := by
    intro h
    exact (hXcentral a h (openSegment_subset_segment ℝ _ _ hacross)).elim ha_va ha_wa
  have hnot : ¬segment ℝ va wa ⊆ X := fun h ↦ haX (h (openSegment_subset_segment ℝ _ _ hacross))
  have hQX : Q ⊆ X := fun _ hz ↦ Or.inl (Or.inl (Or.inl (Or.inl hz)))
  have hEX : (Metric.closedBall (0 : ℂ) 2)ᶜ ⊆ X := fun _ hz ↦ Or.inl (Or.inl (Or.inl (Or.inr hz)))
  have hA₀X : A₀ ⊆ X := fun _ hz ↦ Or.inl (Or.inl (Or.inr hz))
  have hA₁X : A₁ ⊆ X := fun _ hz ↦ Or.inl (Or.inr hz)
  have hRX : R ⊆ X := fun _ hz ↦ Or.inr hz
  have hchain : Relation.ReflTransGen (fun p q ↦ segment ℝ p q ⊆ X) va wa := by
    have hstart : Relation.ReflTransGen (fun p q ↦ segment ℝ p q ⊆ X) va ai :=
      .single (by simpa only [segment_symm] using hA₀X)
    have hmid : Relation.ReflTransGen (fun p q ↦ segment ℝ p q ⊆ X) ai bi :=
      Relation.ReflTransGen.mono (fun p q hpq ↦ by
        intro z hz
        exact hQX (Set.mem_iUnion.mpr ⟨(p,q),Set.mem_iUnion.mpr ⟨hpq,hz⟩⟩)) _ _ hSwalk
    have hbout : Relation.ReflTransGen (fun p q ↦ segment ℝ p q ⊆ X) bi ((4 : ℝ) • b) := .single hRX
    have hout : Relation.ReflTransGen (fun p q ↦ segment ℝ p q ⊆ X) ((4 : ℝ) • a) ((4 : ℝ) • b) :=
      Relation.ReflTransGen.mono (fun _ _ h ↦ h.trans hEX) _ _ hexterior_far
    have houtrev : Relation.ReflTransGen (fun p q ↦ segment ℝ p q ⊆ X) ((4 : ℝ) • b) ((4 : ℝ) • a) := by
      exact Relation.ReflTransGen.mono (fun _ _ h ↦ by simpa only [Function.swap, segment_symm] using h) _ _ (Relation.ReflTransGen.swap _ _ hout)
    have hfinish : Relation.ReflTransGen (fun p q ↦ segment ℝ p q ⊆ X) ((4 : ℝ) • a) wa :=
      .single (by simpa only [segment_symm] using hA₁X)
    exact hstart.trans (hmid.trans (hbout.trans (houtrev.trans hfinish)))
  have hradavoid (z : ℂ) (η : ℝ) (hη : 0 < η ∧ η < 1)
      (hcoll : Disjoint (segment ℝ z ((1-η) • z)) K)
      (hout : Disjoint (segment ℝ z ((4 : ℝ) • z)) K) :
      Disjoint (segment ℝ ((1-η) • z) ((4 : ℝ) • z)) K := by
    apply Set.disjoint_left.mpr
    intro y hy hyK
    obtain ⟨t,ht,rfl⟩ := (radial_segment_mem_iff (by linarith : 1-η ≤ 4)).mp hy
    by_cases ht1 : t ≤ 1
    · apply Set.disjoint_left.mp hcoll _ hyK
      rw [segment_symm]
      simpa only [one_smul] using (radial_segment_mem_iff (by linarith : 1-η ≤ 1)).mpr ⟨t,⟨ht.1,ht1⟩,rfl⟩
    · apply Set.disjoint_left.mp hout _ hyK
      simpa only [one_smul] using (radial_segment_mem_iff (by norm_num : (1 : ℝ) ≤ 4)).mpr ⟨t,⟨le_of_not_ge ht1,ht.2⟩,rfl⟩
  have hradA := hradavoid a eta_a heta_a hcollar_a (houteravoid a (by simp))
  have hradB := hradavoid b eta_b heta_b hcollar_b (houteravoid b (by simp))
  have hAsub (l h : ℝ) (hl : 1-eta_a ≤ l) (hlh : l ≤ h) (hh : h ≤ 4) :
      segment ℝ (l • a) (h • a) ⊆ segment ℝ ai ((4 : ℝ) • a) := by
    intro z hz
    obtain ⟨t,ht,rfl⟩ := (radial_segment_mem_iff hlh).mp hz
    exact (radial_segment_mem_iff (by linarith : 1-eta_a ≤ 4)).mpr ⟨t,⟨hl.trans ht.1,ht.2.trans hh⟩,rfl⟩
  have hXK : Disjoint X K := by
    apply Set.disjoint_left.mpr
    intro z hz hzK
    rcases hz with (((hz | hz) | hz) | hz) | hz
    · exact (hSdisk hz).2 hzK
    · exact hz (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) (hKdisk hzK))
    · exact Set.disjoint_left.mp hradA (hAsub _ _ le_rfl (by linarith) (by linarith) hz) hzK
    · exact Set.disjoint_left.mp hradA (hAsub _ _ (by linarith [heta_a.1]) hε4.le le_rfl hz) hzK
    · exact Set.disjoint_left.mp hradB hz hzK
  have hcK : Disjoint (segment ℝ va wa) K :=
    hradA.mono_left (hAsub _ _ (by linarith) (by linarith) hε4.le)
  have hXcircle : ∀ z ∈ X, ‖z‖ = 1 → z = b := by
    intro z hz hzn
    rcases hz with (((hz | hz) | hz) | hz) | hz
    · have hlt : ‖z‖ < 1 := by simpa [Metric.mem_ball,dist_zero_right] using (hSdisk hz).1
      linarith
    · have hlt : 2 < ‖z‖ := by simpa [Metric.mem_closedBall,dist_zero_right] using hz
      linarith
    · obtain ⟨t,ht,_,hnt⟩ := radial_segment_norm han hai.le (by linarith : 1-eta_a ≤ 1-ε) hz
      linarith [ht.2]
    · obtain ⟨t,ht,_,hnt⟩ := radial_segment_norm han hwa.le hε4.le hz
      linarith [ht.1]
    · obtain ⟨t,ht,hzt,hnt⟩ := radial_segment_norm hbn hbi.le (by linarith [heta_b.1] : 1-eta_b ≤ 4) hz
      have ht1 : t = 1 := hnt.symm.trans hzn
      simpa only [ht1,one_smul] using hzt
  have hccircle : ∀ z ∈ segment ℝ va wa, ‖z‖ = 1 → z = a := by
    intro z hz hzn
    obtain ⟨t,_,hzt,hnt⟩ := radial_segment_norm han hva.le (by linarith : 1-ε ≤ 1+ε) hz
    have ht1 : t = 1 := hnt.symm.trans hzn
    simpa only [ht1,one_smul] using hzt
  obtain ⟨n,p,hpinj,hpnondeg,hinter,hpzero,hplast,hothers,hshort⟩ :=
    segment_chain_polygon_closure X va wa hva_ne hXcentral hnot hchain
  have hlastedge : p.edgeSet ℝ (Fin.last (n+2)) = segment ℝ wa va := by
    simp only [Polygon.edgeSet,finRotate_last,hplast,hpzero,affineSegment_eq_segment]
  have hvaN : ‖va‖ = 1-ε := by rw [show va = (1-ε) • a from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos hva,han,mul_one]
  have hwaN : ‖wa‖ = 1+ε := by rw [show wa = (1+ε) • a from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos hwa,han,mul_one]
  obtain ⟨i,z,hi,hzi,hzn⟩ := polygon_connector_meets_unit_sphere p
    (by rw [hpzero,hvaN]; linarith) (by rw [hplast,hwaN]; linarith)
  have hzb : z = b := hXcircle z (hothers i hi hzi) hzn
  subst z
  have hbCross : ∃ i : Fin (n+3), i ≠ Fin.last (n+2) ∧ b ∈ p.edgeSet ℝ i := ⟨i,hi,hzi⟩
  have hbva : b ≠ va := by intro h; have := congrArg norm h; rw [hbn,hvaN] at this; linarith
  have hbwa : b ≠ wa := by intro h; have := congrArg norm h; rw [hbn,hwaN] at this; linarith
  have hbAlarge : b ∉ segment ℝ ai ((4 : ℝ) • a) := by
    intro h
    obtain ⟨t,ht,hbt,hnt⟩ := radial_segment_norm han hai.le (by linarith [heta_a.1] : 1-eta_a ≤ 4) h
    have ht1 : t = 1 := hnt.symm.trans hbn
    exact hab (by simpa [ht1] using hbt.symm)
  have hAclosed : IsClosed (segment ℝ ai ((4 : ℝ) • a)) := by
    rw [← convexHull_pair]
    exact ((Set.finite_singleton ((4 : ℝ) • a)).insert ai).isCompact_convexHull ℝ |>.isClosed
  obtain ⟨δA,hδA,hδAs⟩ := Metric.mem_nhds_iff.mp (hAclosed.isOpen_compl.mem_nhds hbAlarge)
  obtain ⟨δQ,hδQ,hδQs⟩ := hclearance b (by simp)
  have hlocal : ∃ δ > 0, ∀ z ∈ X, z ∈ Metric.ball b δ → z ∈ Submodule.span ℝ {b} := by
    refine ⟨min δA (min δQ (1/2)),lt_min hδA (lt_min hδQ (by norm_num)),?_⟩
    intro z hz hzb
    have hzA := Metric.ball_subset_ball (min_le_left δA _) hzb
    have hzQ := Metric.ball_subset_ball ((min_le_right δA _).trans (min_le_left δQ _)) hzb
    have hzh := Metric.ball_subset_ball ((min_le_right δA _).trans (min_le_right δQ _)) hzb
    rcases hz with (((hz | hz) | hz) | hz) | hz
    · exact (hδQs (Metric.ball_subset_closedBall hzQ) hz).elim
    · have hfar : 2 < ‖z‖ := by simpa [Metric.mem_closedBall,dist_zero_right] using hz
      have hnear : ‖z-b‖ < 1/2 := by simpa [Metric.mem_ball,dist_eq_norm] using hzh
      have htri := norm_add_le (z-b) b
      rw [sub_add_cancel,hbn] at htri
      linarith
    · exact (hδAs hzA (hAsub _ _ le_rfl (by linarith) (by linarith) hz)).elim
    · exact (hδAs hzA (hAsub _ _ (by linarith [heta_a.1]) hε4.le le_rfl hz)).elim
    · obtain ⟨t,_,rfl⟩ := (radial_segment_mem_iff (by linarith [heta_b.1] : 1-eta_b ≤ 4)).mp hz
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b)
  have hbcontact := polygon_shortest_radial_contact p X b hpinj hothers hshort
    (hpzero.symm ▸ hbva) (hplast.symm ▸ hbwa) hlocal hbCross
  refine ⟨n+3,p,by omega,hpinj,hpnondeg,hinter,?_,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro z hz hzK
    obtain ⟨j,hj⟩ := mem_iUnion.mp hz
    by_cases hjL : j = Fin.last (n+2)
    · subst j
      rw [hlastedge,segment_symm] at hj
      exact Set.disjoint_left.mp hcK hj hzK
    · exact Set.disjoint_left.mp hXK (hothers j hjL hj) hzK
  · apply subset_antisymm
    · rintro z ⟨hz,hzs⟩
      have hzn : ‖z‖ = 1 := by simpa [Metric.mem_sphere,dist_zero_right] using hzs
      obtain ⟨j,hj⟩ := mem_iUnion.mp hz
      by_cases hjL : j = Fin.last (n+2)
      · subst j
        rw [hlastedge,segment_symm] at hj
        exact Or.inl (hccircle z hj hzn)
      · exact Or.inr (hXcircle z (hothers j hjL hj) hzn)
    · intro z hz
      rcases hz with hz | hz
      · subst z
        exact ⟨mem_iUnion.mpr ⟨Fin.last (n+2), by rw [hlastedge,segment_symm]; exact openSegment_subset_segment ℝ _ _ hacross⟩,ha.1⟩
      · subst z
        exact ⟨mem_iUnion.mpr ⟨i,hzi⟩,hb.1⟩
  · intro z hz
    rcases hz with hz | hz
    · subst z
      refine ⟨Fin.last (n+2),1+ε,1-ε,hplast,?_,?_⟩
      · simpa only [finRotate_last] using hpzero
      · simpa only [finRotate_last,hplast,hpzero,openSegment_symm] using hacross
    · subst z
      exact hbcontact



end HolomorphicAnosov
