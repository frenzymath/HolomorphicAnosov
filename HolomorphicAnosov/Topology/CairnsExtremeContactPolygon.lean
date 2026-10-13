import HolomorphicAnosov.Topology.CairnsSimplePolygonSchoenflies
import HolomorphicAnosov.Topology.CairnsExtremeContactOrdinateExtrema
import HolomorphicAnosov.Topology.CairnsExtremeContactStrictExtrema
import HolomorphicAnosov.Topology.CairnsExtremeContactRectangleBounds
import HolomorphicAnosov.Topology.CairnsExtremeContactSegmentTips
import Mathlib.Analysis.Complex.Convex

set_option maxHeartbeats 1500000

open Set Metric

namespace HolomorphicAnosov

/-- Cairns's first Section 5 construction supplies a finite simple polygon whose
boundary meets an embedded circle only at two distinct extreme-contact points.

Source: Stewart S. Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem*
(1951), §5, printed p.866, paragraph after Lemma 5.1. The explicit six-vertex
construction and component-containment argument below expand the source's phrase
“easy to define”; the expansion is agent-written. DAG node:
`topo.cairns_extreme_contact_polygon_g6`.

Proof. Compactness supplies upper and lower ordinate contacts P₁,P₂, and an embedded
circle cannot have constant ordinate, so m=P₂.im<M=P₁.im. Choose L and R strictly
outside its real-coordinate range. The cyclic vertices are (L,M+1), P₁, (R,M+1),
(R,m−1), P₂, (L,m−1). The two upper edges have ordinate at least M, the lower two
have ordinate at most m, and the other edges have real coordinate L or R. Opposite
chains are disjoint; two neighboring edges have overlapping coordinate intervals
only at their shared endpoint's real coordinate, which forces that endpoint by
the affine segment formula. Thus the vertices and edges form a simple polygon.
The same affine formula shows that each upper or lower edge meets the curve only
at its contact; the vertical edges miss the curve by the strict real bounds.

Apply the finite polygon theorem to obtain bounded region Q and exterior E with
common frontier equal to the polygon. The half-plane re<L lies in E: it is
connected and avoids the polygon, and its unboundedness prevents inclusion in Q.
A neighborhood of the midpoint of the left vertical edge, confined between m and
M and left of R, meets Q by the frontier property. This Q-point has real coordinate
strictly greater than L, since points left of L belong to E and points on L in
this ordinate interval belong to the polygon. Hence the convex open rectangle
S=(L,R)×(m,M) meets Q. It avoids every polygon edge and is connected, so S⊆Q.
The whole curve lies in closure S. Since closure Q=Q∪boundary(p), every curve
point other than P₁,P₂ lies in Q. Connectedness and maximality identify Q as the
complementary component through the point just constructed. This argument allows
multiple points attaining either extreme ordinate; only the chosen contacts lie
on the polygon boundary.
-/
theorem cairns_extreme_contact_polygon
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ) :
    ∃ n : ℕ, ∃ p : Polygon ℂ (n + 1), ∃ P₁ P₂ : ℂ,
      IsSimpleClosedPolygon p ∧
      P₁ ∈ Set.range γ ∧ P₂ ∈ Set.range γ ∧ P₁ ≠ P₂ ∧
      (∀ z ∈ Set.range γ, z.im ≤ P₁.im) ∧
      (∀ z ∈ Set.range γ, P₂.im ≤ z.im) ∧
      (∃ B : Set ℂ,
        Bornology.IsBounded B ∧ IsConnected B ∧ IsOpen B ∧
        (∃ z : ℂ, B = connectedComponentIn (p.boundary ℝ)ᶜ z) ∧
        Set.range γ \ {P₁, P₂} ⊆ B) ∧
      p.boundary ℝ ∩ Set.range γ = {P₁, P₂} := by
  obtain ⟨P₁, P₂, hP₁, hP₂, hmax, hmin⟩ :=
    cairns_extreme_contact_ordinate_extrema γ hγ
  have hP₁₂ := cairns_extreme_contact_distinct_extrema γ hγ P₁ P₂ hP₁ hP₂ hmax hmin
  have hstrict := cairns_extreme_contact_strict_extrema γ hγ P₁ P₂ hP₁ hP₂ hmax hmin hP₁₂
  obtain ⟨L, R, hLR⟩ := cairns_extreme_contact_rectangle_bounds γ hγ
  obtain ⟨hL₁, hR₁⟩ := hLR P₁ hP₁
  obtain ⟨hL₂, hR₂⟩ := hLR P₂ hP₂
  let A : ℂ := ⟨L, P₁.im + 1⟩
  let C : ℂ := ⟨R, P₁.im + 1⟩
  let D : ℂ := ⟨R, P₂.im - 1⟩
  let F : ℂ := ⟨L, P₂.im - 1⟩
  let p : Polygon ℂ 6 := ⟨![A, P₁, C, D, P₂, F]⟩
  have hcoord (U V z : ℂ) (hz : z ∈ segment ℝ U V) :
      min U.re V.re ≤ z.re ∧ z.re ≤ max U.re V.re ∧
      min U.im V.im ≤ z.im ∧ z.im ≤ max U.im V.im := by
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t, ⟨ht₀, ht₁⟩, rfl⟩ := hz
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul,
      Complex.sub_re, Complex.sub_im]
    constructor
    · rcases le_total U.re V.re with h | h <;> simp only [min_eq_left, min_eq_right, h] <;> nlinarith
    constructor
    · rcases le_total U.re V.re with h | h <;> simp only [max_eq_left, max_eq_right, h] <;> nlinarith
    constructor
    · rcases le_total U.im V.im with h | h <;> simp only [min_eq_left, min_eq_right, h] <;> nlinarith
    · rcases le_total U.im V.im with h | h <;> simp only [max_eq_left, max_eq_right, h] <;> nlinarith
  have htip (U V z : ℂ) (hne : U.re ≠ V.re)
      (hz : z ∈ segment ℝ U V) (heq : z.re = U.re) : z = U := by
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    have ht₀ : t = 0 := by
      have heq' : t * (V.re - U.re) = 0 := by
        simpa [AffineMap.lineMap_apply] using heq
      exact (mul_eq_zero.mp heq').resolve_right (sub_ne_zero.mpr hne.symm)
    simp [ht₀]
  have hedges (i : Fin 6) : p.edgeSet ℝ i =
      ![segment ℝ A P₁, segment ℝ P₁ C, segment ℝ C D,
        segment ℝ D P₂, segment ℝ P₂ F, segment ℝ F A] i := by
    fin_cases i <;> simp [p, Polygon.edgeSet, affineSegment_eq_segment, finRotate_apply]
  have hbox (U V z : ℂ) (hz : z ∈ segment ℝ U V)
      (l r b t : ℝ) (hl : l ≤ U.re ∧ l ≤ V.re) (hr : U.re ≤ r ∧ V.re ≤ r)
      (hb : b ≤ U.im ∧ b ≤ V.im) (ht : U.im ≤ t ∧ V.im ≤ t) :
      l ≤ z.re ∧ z.re ≤ r ∧ b ≤ z.im ∧ z.im ≤ t := by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hcoord U V z hz
    exact ⟨(le_min hl.1 hl.2).trans h₁, h₂.trans (max_le hr.1 hr.2),
      (le_min hb.1 hb.2).trans h₃, h₄.trans (max_le ht.1 ht.2)⟩
  have hbounds (i : Fin 6) (z : ℂ) (hz : z ∈ p.edgeSet ℝ i) :
      ![L, P₁.re, R, P₂.re, L, L] i ≤ z.re ∧
      z.re ≤ ![P₁.re, R, R, R, P₂.re, L] i ∧
      ![P₁.im, P₁.im, P₂.im - 1, P₂.im - 1, P₂.im - 1, P₂.im - 1] i ≤ z.im ∧
      z.im ≤ ![P₁.im + 1, P₁.im + 1, P₁.im + 1, P₂.im, P₂.im, P₁.im + 1] i := by
    rw [hedges] at hz
    fin_cases i <;> dsimp at hz ⊢
    all_goals apply hbox _ _ z hz <;> dsimp [A, C, D, F] <;> constructor <;> linarith
  have hsimple : IsSimpleClosedPolygon p := by
    refine ⟨by norm_num, ?_, ?_, ?_⟩
    · intro i j hij
      have hre := congrArg Complex.re hij
      have him := congrArg Complex.im hij
      fin_cases i <;> fin_cases j <;> dsimp [p, A, C, D, F] at hre him ⊢ <;> first | rfl | (exfalso; linarith)
    · intro i hi
      have hre := congrArg Complex.re hi
      have him := congrArg Complex.im hi
      fin_cases i <;> norm_num [p, A, C, D, F, finRotate_apply] at hre him <;> linarith
    · intro i j hij z hz
      have hi := hbounds i z hz.1
      have hj := hbounds j z hz.2
      rw [hedges i, hedges j] at hz
      fin_cases i <;> fin_cases j
      all_goals try { exact (hij rfl).elim }
      all_goals norm_num [finRotate_apply] at hi hj ⊢
      all_goals dsimp at hz
      all_goals try { exfalso; linarith [hi.1, hi.2.1, hi.2.2.1, hi.2.2.2,
        hj.1, hj.2.1, hj.2.2.1, hj.2.2.2] }
      · refine ⟨1, by norm_num, ?_⟩
        change P₁ = z
        symm
        apply htip P₁ C z (by dsimp [A, C, D, F]; linarith)
        · exact hz.2
        · try dsimp [A, C, D, F]
          linarith [hi.1, hi.2.1, hj.1, hj.2.1]
      · refine ⟨0, by norm_num, ?_⟩
        change A = z
        symm
        apply htip A P₁ z (by dsimp [A, C, D, F]; linarith)
        · exact hz.1
        · try dsimp [A, C, D, F]
          linarith [hi.1, hi.2.1, hj.1, hj.2.1]
      · refine ⟨1, by norm_num, ?_⟩
        change P₁ = z
        symm
        apply htip P₁ C z (by dsimp [A, C, D, F]; linarith)
        · exact hz.1
        · try dsimp [A, C, D, F]
          linarith [hi.1, hi.2.1, hj.1, hj.2.1]
      · refine ⟨2, by norm_num, ?_⟩
        change C = z
        symm
        apply htip C P₁ z (by dsimp [A, C, D, F]; linarith)
        · simpa only [segment_symm] using hz.1
        · try dsimp [A, C, D, F]
          linarith [hi.1, hi.2.1, hj.1, hj.2.1]
      · refine ⟨2, by norm_num, ?_⟩
        change C = z
        symm
        apply htip C P₁ z (by dsimp [A, C, D, F]; linarith)
        · simpa only [segment_symm] using hz.2
        · try dsimp [A, C, D, F]
          linarith [hi.1, hi.2.1, hj.1, hj.2.1]
      · refine ⟨3, by norm_num, ?_⟩
        change D = z
        symm
        apply htip D P₂ z (by dsimp [A, C, D, F]; linarith)
        · exact hz.2
        · try dsimp [A, C, D, F]
          linarith [hi.1, hi.2.1, hj.1, hj.2.1]
      · refine ⟨3, by norm_num, ?_⟩
        change D = z
        symm
        apply htip D P₂ z (by dsimp [A, C, D, F]; linarith)
        · exact hz.1
        · try dsimp [A, C, D, F]
          linarith [hi.1, hi.2.1, hj.1, hj.2.1]
      · refine ⟨4, by norm_num, ?_⟩
        change P₂ = z
        symm
        apply htip P₂ F z (by dsimp [A, C, D, F]; linarith)
        · exact hz.2
        · try dsimp [A, C, D, F]
          linarith [hi.1, hi.2.1, hj.1, hj.2.1]
      · refine ⟨4, by norm_num, ?_⟩
        change P₂ = z
        symm
        apply htip P₂ F z (by dsimp [A, C, D, F]; linarith)
        · exact hz.1
        · try dsimp [A, C, D, F]
          linarith [hi.1, hi.2.1, hj.1, hj.2.1]
      · refine ⟨5, by norm_num, ?_⟩
        change F = z
        symm
        apply htip F P₂ z (by dsimp [A, C, D, F]; linarith)
        · simpa only [segment_symm] using hz.1
        · try dsimp [A, C, D, F]
          linarith [hi.1, hi.2.1, hj.1, hj.2.1]
      · refine ⟨0, by norm_num, ?_⟩
        change A = z
        symm
        apply htip A P₁ z (by dsimp [A, C, D, F]; linarith)
        · exact hz.2
        · try dsimp [A, C, D, F]
          linarith [hi.1, hi.2.1, hj.1, hj.2.1]
      · refine ⟨5, by norm_num, ?_⟩
        change F = z
        symm
        apply htip F P₂ z (by dsimp [A, C, D, F]; linarith)
        · simpa only [segment_symm] using hz.2
        · try dsimp [A, C, D, F]
          linarith [hi.1, hi.2.1, hj.1, hj.2.1]
  have hinter : p.boundary ℝ ∩ Set.range γ = {P₁, P₂} := by
    ext z
    constructor
    · rintro ⟨hz, hzγ⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      rw [hedges] at hi
      fin_cases i
      · have heq := cairns_upper_contact_segment_tip P₁ A z (by dsimp [A]; linarith)
          (by simpa [segment_symm] using hi) (hmax z hzγ)
        simp [heq]
      · have heq := cairns_upper_contact_segment_tip P₁ C z (by dsimp [C]; linarith)
          hi (hmax z hzγ)
        simp [heq]
      · have hc := hcoord C D z hi
        dsimp [C, D] at hc
        obtain ⟨_, hlt⟩ := hLR z hzγ
        simp only [min_self] at hc
        linarith [hc.1]
      · have heq := cairns_lower_contact_segment_tip P₂ D z (by dsimp [D]; linarith)
          (by simpa [segment_symm] using hi) (hmin z hzγ)
        simp [heq]
      · have heq := cairns_lower_contact_segment_tip P₂ F z (by dsimp [F]; linarith)
          hi (hmin z hzγ)
        simp [heq]
      · have hc := hcoord F A z hi
        dsimp [F, A] at hc
        obtain ⟨hlt, _⟩ := hLR z hzγ
        simp only [max_self] at hc
        linarith [hc.2.1]
    · intro hz
      rcases (show z = P₁ ∨ z = P₂ by simpa using hz) with rfl | rfl
      · refine ⟨mem_iUnion.mpr ⟨1, ?_⟩, hP₁⟩
        rw [hedges]
        exact left_mem_segment ℝ _ _
      · refine ⟨mem_iUnion.mpr ⟨4, ?_⟩, hP₂⟩
        rw [hedges]
        exact left_mem_segment ℝ _ _

  refine ⟨5, p, P₁, P₂, hsimple, hP₁, hP₂, hP₁₂, hmax, hmin, ?_, hinter⟩
  obtain ⟨Q, E, hQne, hEne, hQE, hun, hdisj, hcomp, hQconn, hEconn,
    hQopen, hEopen, hQbound, hEbound, hQfront, hEfront, hQclose, hrest⟩ :=
    cairns_simple_polygon_schoenflies p hsimple
  have hQsub : Q ⊆ (p.boundary ℝ)ᶜ := fun z hz ↦ hun ▸ Or.inl hz
  have hleftsub : {z : ℂ | z.re < L} ⊆ E := by
    have havoid : {z : ℂ | z.re < L} ⊆ Q ∪ E := by
      rw [hun]
      intro z hz hb
      change z.re < L at hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hb
      have hb := (hbounds i z hi).1
      fin_cases i <;> dsimp at hb <;> linarith
    rcases (convex_halfSpace_re_lt L).isPreconnected.subset_or_subset
        hQopen hEopen hdisj havoid with h | h
    · obtain ⟨K, hK⟩ := hQbound.exists_norm_le
      let z : ℂ := ⟨-(|L| + |K| + 1), 0⟩
      have hz : z.re < L := by dsimp [z]; linarith [neg_abs_le L, abs_nonneg K]
      have hnorm := hK z (h hz)
      have habs := (neg_le_abs z.re).trans (Complex.abs_re_le_norm z)
      dsimp [z] at habs
      exfalso
      linarith [abs_nonneg L, le_abs_self K]
    · exact h
  let S : Set ℂ := {z | (L < z.re ∧ z.re < R) ∧ P₂.im < z.im ∧ z.im < P₁.im}
  have hSconn : IsPreconnected S :=
    (((convex_halfSpace_re_gt L).inter (convex_halfSpace_re_lt R)).inter
      ((convex_halfSpace_im_gt P₂.im).inter (convex_halfSpace_im_lt P₁.im))).isPreconnected
  have hSsub : S ⊆ Q ∪ E := by
    rw [hun]
    intro z hz hb
    obtain ⟨i, hi⟩ := mem_iUnion.mp hb
    have hb := hbounds i z hi
    fin_cases i <;> dsimp at hb <;> dsimp [S] at hz <;>
      linarith [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  let w : ℂ := ⟨L, (P₁.im + P₂.im) / 2⟩
  have hw : w ∈ p.boundary ℝ := by
    refine mem_iUnion.mpr ⟨5, ?_⟩
    rw [hedges]
    change w ∈ segment ℝ F A
    rw [segment_eq_image_lineMap]
    let t := (w.im - F.im) / (A.im - F.im)
    have hd : 0 < A.im - F.im := by dsimp [A, F]; linarith
    refine ⟨t, ⟨?_, ?_⟩, ?_⟩
    · apply div_nonneg _ hd.le
      dsimp [w, F]; linarith
    · apply (div_le_one hd).mpr
      dsimp [w, F, A]; linarith
    · apply Complex.ext
      · simp [AffineMap.lineMap_apply, w, F, A]
      · simp only [AffineMap.lineMap_apply, Complex.add_im, Complex.smul_im,
          smul_eq_mul, Complex.sub_im, vsub_eq_sub, vadd_eq_add]
        dsimp [t]
        rw [div_mul_cancel₀ _ hd.ne']
        ring
  let O : Set ℂ := {z | z.re < R ∧ P₂.im < z.im ∧ z.im < P₁.im}
  have hOopen : IsOpen O :=
    (isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const))
  have hwO : w ∈ O := by dsimp [O, w]; exact ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨v, hvO, hvQ⟩ := mem_closure_iff.mp
    (frontier_subset_closure (hQfront.symm ▸ hw)) O hOopen hwO
  have hvleft : L < v.re := by
    rcases lt_trichotomy v.re L with h | h | h
    · exact (Set.disjoint_left.mp hdisj hvQ (hleftsub h)).elim
    · have hvboundary : v ∈ p.boundary ℝ := by
        refine mem_iUnion.mpr ⟨5, ?_⟩
        rw [hedges]
        change v ∈ segment ℝ F A
        rw [segment_eq_image_lineMap]
        let t := (v.im - F.im) / (A.im - F.im)
        have hd : 0 < A.im - F.im := by dsimp [A, F]; linarith
        refine ⟨t, ⟨?_, ?_⟩, ?_⟩
        · apply div_nonneg _ hd.le
          dsimp [F]; linarith [hvO.2.1]
        · apply (div_le_one hd).mpr
          dsimp [F, A]; linarith [hvO.2.2]
        · apply Complex.ext
          · simpa [AffineMap.lineMap_apply, F, A] using h.symm
          · simp only [AffineMap.lineMap_apply, Complex.add_im, Complex.smul_im,
              smul_eq_mul, Complex.sub_im, vsub_eq_sub, vadd_eq_add]
            dsimp [t]
            rw [div_mul_cancel₀ _ hd.ne']
            ring
      exact (hQsub hvQ hvboundary).elim
    · exact h
  have hvS : v ∈ S := ⟨⟨hvleft, hvO.1⟩, hvO.2⟩
  have hSQ : S ⊆ Q := by
    rcases hSconn.subset_or_subset hQopen hEopen hdisj hSsub with h | h
    · exact h
    · exact (Set.disjoint_left.mp hdisj hvQ (h hvS)).elim
  have hQcomponent : Q = connectedComponentIn (p.boundary ℝ)ᶜ v := by
    apply Subset.antisymm (hQconn.isPreconnected.subset_connectedComponentIn hvQ hQsub)
    have hcsub : connectedComponentIn (p.boundary ℝ)ᶜ v ⊆ Q ∪ E :=
      hun.symm ▸ connectedComponentIn_subset _ _
    rcases isPreconnected_connectedComponentIn.subset_or_subset
        hQopen hEopen hdisj hcsub with h | h
    · exact h
    · exact (Set.disjoint_left.mp hdisj hvQ (h (mem_connectedComponentIn (hQsub hvQ)))).elim
  refine ⟨Q, hQbound, hQconn, hQopen, ⟨v, hQcomponent⟩, ?_⟩
  intro z hz
  have hzc : z ∉ p.boundary ℝ := fun hb ↦ hz.2 (hinter ▸ ⟨hb, hz.1⟩)
  have hzS : z ∈ closure S := by
    change z ∈ closure (Complex.reProdIm (Ioo L R) (Ioo P₂.im P₁.im))
    rw [Complex.closure_reProdIm, closure_Ioo (by linarith : L ≠ R), closure_Ioo hstrict.ne]
    exact ⟨⟨(hLR z hz.1).1.le, (hLR z hz.1).2.le⟩, hmin z hz.1, hmax z hz.1⟩
  have hzQ := closure_mono hSQ hzS
  rw [hQclose] at hzQ
  exact hzQ.resolve_right hzc


end HolomorphicAnosov
