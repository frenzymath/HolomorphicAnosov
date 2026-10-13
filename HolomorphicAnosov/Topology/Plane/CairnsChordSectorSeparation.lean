import HolomorphicAnosov.Topology.Plane.ChordLocalHalfDisks
import HolomorphicAnosov.Topology.FrontierConnectedComponentIn
import HolomorphicAnosov.Topology.CairnsMarkedArcSeparation
import HolomorphicAnosov.Topology.LocalPositiveSideComponent
import HolomorphicAnosov.Topology.TwoComponentsExhaustLocalCover
import HolomorphicAnosov.Topology.PositiveCoordinateFrontierPoint
import HolomorphicAnosov.Topology.ComponentConnectionFrontierContacts
import HolomorphicAnosov.Topology.Plane.ChordTransverseStub

/-! # Sectors cut by a chord of an embedded circle

Source: Cairns (1951), Lemma 3.1(A)–(C) and its corollary, pp.861–862.
The bounded complementary component is input data. The proof uses finite-polygon
separation and compact-obstacle marked closure. It does not use a later arbitrary
Jordan or Schoenflies theorem.
-/

namespace HolomorphicAnosov
open Set

/-- A chord of a bounded complementary component cuts that component into two
open connected sectors, with the prescribed boundary-arc labels and opposite
local straight-line sides.

Source: Cairns (1951), Lemma 3.1 and corollary, pp.861–862. The polygon contradiction
follows the source. The explicit component propagation, compact-maximum frontier
selection, and frontier-contact connection arguments below expand its omitted
exhaustion and labeling steps; their reusable lemmas are marked agent-written.

1. The curve image is compact and closed. Its component a is open and connected. The chord endpoints lie on the curve, so they are outside a, and a minus the open chord equals a minus the closed chord; this set V is open. The frontier of a is contained in the curve, and the frontier of every component of V is contained in the curve union the closed chord. The local-half-disk theorem supplies, at every interior chord point, nonempty connected positive and negative half-disks for the affine coordinate F(w)=Im(conj(B-A)(w-A)). This coordinate is continuous and open and vanishes on the chord.

2. Apply local positive-side component constancy to F and to -F along the connected open chord. It gives components betaP and betaN of V which contain the respective local half-disks at every chord point. At a midpoint m, intersect the two chosen neighborhoods with a and apply the local-half-disk theorem once more. This gives one ball whose positive and negative halves lie respectively in betaP and betaN.

3. Choose a point in the positive half-ball and reflect it through m. The transverse-stub lemma gives endpoints xp and xm in the two half-balls, a stub lying in a, and its unique transverse meeting m with the chord. If betaP and betaN met, component maximality would connect xp to xm in V and hence in the complement of the curve union the chord. Apply marked-arc separation with the whole compact curve as obstacle and either original arc as its joining path. This is impossible, proving disjointness.

4. The open chord is relatively closed in a because its closure lies in the closed chord and the endpoints are outside a. The union betaP union betaN union the open chord is a neighborhood of every chord point by the half-disk decomposition. The frontiers of both components avoid V. The two-component local-cover theorem therefore shows V=betaP union betaN. Every component of V is one of these two by maximality.

5. Let Ti be the image of the open parameter interval of arc i. Each Ti is preconnected, avoids the closed chord, and avoids the other closed arc: the original closed arcs meet only at their endpoints, while the chord interior lies in a. Every point of the curve outside the chord lies in T1 or T2. Suppose both sector frontiers met T1. The frontier-contact connection theorem, using T1 to join the two sectors, would connect xm to xp in the complement of the other closed arc union the chord. Marked-arc separation applied to that other closed arc rules this out. The same reasoning applies with T1,T2 interchanged.

6. Both sectors are bounded as subsets of a. Maximize F on the compact closure of betaP, using its positive stub endpoint, and maximize -F on the closure of betaN, using its negative endpoint. The positive-coordinate frontier theorem gives a frontier point of each sector off the full chord line. By the general frontier bound these points lie in T1 or T2. The preceding no-shared-contact result forces opposite labels. The same result excludes every contact of a sector frontier with the opposite open arc, leaving only the chord and its own closed arc. Choose the ordered pair according to those labels; if the order is reversed, swap the side disjunction. All required conclusions follow.
-/
theorem cairns_chord_sector_separation
    (c : Circle → ℂ) (hc : Topology.IsEmbedding c)
    (p q : Circle) (hpq : p ≠ q)
    (arc₁ arc₂ : Set.Icc (0 : ℝ) 1 → Circle)
    (hArc₁ : Topology.IsEmbedding arc₁) (hArc₂ : Topology.IsEmbedding arc₂)
    (hStart₁ : arc₁ ⟨0, by simp⟩ = p) (hEnd₁ : arc₁ ⟨1, by simp⟩ = q)
    (hStart₂ : arc₂ ⟨0, by simp⟩ = p) (hEnd₂ : arc₂ ⟨1, by simp⟩ = q)
    (hArcsCover : Set.range arc₁ ∪ Set.range arc₂ = Set.univ)
    (hArcsMeet : Set.range arc₁ ∩ Set.range arc₂ = {p, q})
    (a : Set ℂ) (_haNonempty : a.Nonempty) (haBounded : Bornology.IsBounded a)
    (haComponent : ∃ z ∈ a, connectedComponentIn (Set.range c)ᶜ z = a)
    (hChord : openSegment ℝ (c p) (c q) ⊆ a) :
    ∃ β₁ β₂ : Set ℂ,
      β₁.Nonempty ∧ β₂.Nonempty ∧ IsConnected β₁ ∧ IsConnected β₂ ∧
      IsOpen β₁ ∧ IsOpen β₂ ∧ Disjoint β₁ β₂ ∧
      a \ openSegment ℝ (c p) (c q) = β₁ ∪ β₂ ∧
      (∀ z ∈ a \ openSegment ℝ (c p) (c q),
        connectedComponentIn (a \ openSegment ℝ (c p) (c q)) z = β₁ ∨
          connectedComponentIn (a \ openSegment ℝ (c p) (c q)) z = β₂) ∧
      frontier β₁ ⊆ segment ℝ (c p) (c q) ∪ c '' Set.range arc₁ ∧
      frontier β₂ ⊆ segment ℝ (c p) (c q) ∪ c '' Set.range arc₂ ∧
      ∀ z ∈ openSegment ℝ (c p) (c q), ∃ r : ℝ, 0 < r ∧
        Metric.ball z r ⊆ a ∧
        let positiveSide := {w ∈ Metric.ball z r |
          0 < (star (c q - c p) * (w - c p)).im}
        let negativeSide := {w ∈ Metric.ball z r |
          (star (c q - c p) * (w - c p)).im < 0}
        positiveSide.Nonempty ∧ negativeSide.Nonempty ∧
          Metric.ball z r \ openSegment ℝ (c p) (c q) = positiveSide ∪ negativeSide ∧
          ((positiveSide ⊆ β₁ ∧ negativeSide ⊆ β₂) ∨
            (positiveSide ⊆ β₂ ∧ negativeSide ⊆ β₁)) := by
  classical
  have hcurveCompact : IsCompact (range c) := isCompact_range hc.continuous
  have haSub : a ⊆ (range c)ᶜ := by
    obtain ⟨x,hx,he⟩ := haComponent
    rw [← he]
    exact connectedComponentIn_subset _ _
  have haOpen : IsOpen a := by
    obtain ⟨x,hx,he⟩ := haComponent
    rw [← he]
    exact hcurveCompact.isClosed.isOpen_compl.connectedComponentIn
  have haConnected : IsConnected a := by
    obtain ⟨x,hx,he⟩ := haComponent
    rw [← he]
    exact isConnected_connectedComponentIn_iff.mpr (haSub hx)
  have hremove : a \ openSegment ℝ (c p) (c q) = a \ segment ℝ (c p) (c q) := by
    ext z
    constructor
    · rintro ⟨hza,hzo⟩
      refine ⟨hza, ?_⟩
      rw [← insert_endpoints_openSegment]
      rintro (rfl | rfl | hz)
      · exact haSub hza ⟨p,rfl⟩
      · exact haSub hza ⟨q,rfl⟩
      · exact hzo hz
    · rintro ⟨hza,hzs⟩
      exact ⟨hza,fun hz ↦ hzs (openSegment_subset_segment ℝ _ _ hz)⟩
  have hcutOpen : IsOpen (a \ openSegment ℝ (c p) (c q)) := by
    rw [hremove]
    have hseg : IsCompact (segment ℝ (c p) (c q)) := by
      rw [← convexHull_pair]
      exact ((Set.finite_singleton (c q)).insert (c p)).isCompact_convexHull ℝ
    exact haOpen.sdiff hseg.isClosed
  have hcomponentOpen (z : ℂ) :
      IsOpen (connectedComponentIn (a \ openSegment ℝ (c p) (c q)) z) :=
    hcutOpen.connectedComponentIn
  have hlocalHalfDisks (z : ℂ) (hz : z ∈ openSegment ℝ (c p) (c q)) :=
    chord_local_half_disks (hc.injective.ne hpq) hz haOpen (hChord hz)
  have haFrontier : frontier a ⊆ range c := by
    obtain ⟨x, hx, he⟩ := haComponent
    rw [← he]
    simpa only [compl_compl] using
      frontier_connectedComponentIn_subset_compl hcurveCompact.isClosed.isOpen_compl x
  have hcomponentFrontier (x : ℂ) :
      frontier (connectedComponentIn (a \ openSegment ℝ (c p) (c q)) x) ⊆
        range c ∪ segment ℝ (c p) (c q) := by
    intro y hy
    have hycl : y ∈ closure a :=
      closure_mono ((connectedComponentIn_subset _ _).trans sdiff_subset)
        (frontier_subset_closure hy)
    have hynot := frontier_connectedComponentIn_subset_compl hcutOpen x hy
    by_cases hya : y ∈ a
    · right
      apply openSegment_subset_segment ℝ _ _
      by_contra hno
      exact hynot ⟨hya, hno⟩
    · left
      apply haFrontier
      rw [haOpen.frontier_eq]
      exact ⟨hycl, hya⟩
  let A := c p
  let B := c q
  let S := openSegment ℝ A B
  let V := a \ S
  let F : ℂ → ℝ := fun w ↦ (star (B-A) * (w-A)).im
  let L : ℂ →ₗ[ℝ] ℝ := Complex.imLm.comp (LinearMap.mulLeft ℝ (star (B-A)))
  have hFL (w : ℂ) : F w = L w - L A := by
    simp only [F, L, LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_sub, Complex.sub_im]
    rfl
  have hAB : A ≠ B := hc.injective.ne hpq
  have hFopen : IsOpenMap F :=
    Complex.isOpenMap_im.comp
      ((Homeomorph.mulLeft₀ (star (B-A)) (star_ne_zero.mpr (sub_ne_zero.mpr hAB.symm))).isOpenMap.comp
        (Homeomorph.addRight (-A)).isOpenMap)
  have hFcont : Continuous F := by fun_prop
  have hFseg (z : ℂ) (hz : z ∈ segment ℝ A B) : F z = 0 := by
    obtain ⟨t, ht, rfl⟩ := (segment_eq_image' ℝ A B ▸ hz)
    dsimp [F]
    simp only [add_sub_cancel_left]
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
      Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
    ring
  have hSconn : IsConnected S :=
    (convex_openSegment A B).isConnected ⟨midpoint ℝ A B, midpoint_mem_openSegment A B⟩
  have hFzero (z : ℂ) (hz : z ∈ S) : F z = 0 :=
    hFseg z (openSegment_subset_segment ℝ _ _ hz)
  have hPlocal : ∀ z ∈ S, ∃ r : ℝ, 0 < r ∧
      IsConnected (Metric.ball z r ∩ {w | 0 < F w}) ∧
      Metric.ball z r ∩ {w | 0 < F w} ⊆ V := by
    intro z hz
    obtain ⟨r, hr, hball, hp, hn, hpc, hnc, heq⟩ := hlocalHalfDisks z hz
    refine ⟨r, hr, hpc, ?_⟩
    intro w hw
    exact ⟨hball hw.1, fun hs ↦ hw.2.ne' (hFzero w hs)⟩
  have hNlocal : ∀ z ∈ S, ∃ r : ℝ, 0 < r ∧
      IsConnected (Metric.ball z r ∩ {w | 0 < -F w}) ∧
      Metric.ball z r ∩ {w | 0 < -F w} ⊆ V := by
    intro z hz
    obtain ⟨r, hr, hball, hp, hn, hpc, hnc, heq⟩ := hlocalHalfDisks z hz
    refine ⟨r, hr, ?_, ?_⟩
    · have heq : Metric.ball z r ∩ {w | 0 < -F w} =
          {w ∈ Metric.ball z r | F w < 0} := by
        ext w
        change (w ∈ Metric.ball z r ∧ 0 < -F w) ↔ (w ∈ Metric.ball z r ∧ F w < 0)
        simp only [neg_pos]
      rw [heq]
      exact hnc
    · intro w hw
      exact ⟨hball hw.1, fun hs ↦ (neg_pos.mp hw.2).ne (hFzero w hs)⟩
  obtain ⟨xp₀, hxp₀, hpnear⟩ := local_positive_side_component hSconn F hFopen hFzero hPlocal
  obtain ⟨xn₀, hxn₀, hnnear⟩ := local_positive_side_component hSconn (fun w ↦ -F w)
    ((Homeomorph.neg ℝ).isOpenMap.comp hFopen) (by intro z hz; simp [hFzero z hz]) hNlocal
  let βp := connectedComponentIn V xp₀
  let βn := connectedComponentIn V xn₀
  have hβpo : IsOpen βp := hcutOpen.connectedComponentIn
  have hβno : IsOpen βn := hcutOpen.connectedComponentIn
  have hβpc : IsConnected βp := isConnected_connectedComponentIn_iff.mpr hxp₀
  have hβnc : IsConnected βn := isConnected_connectedComponentIn_iff.mpr hxn₀
  have hβps : βp ⊆ V := connectedComponentIn_subset _ _
  have hβns : βn ⊆ V := connectedComponentIn_subset _ _
  have hnear (z : ℂ) (hz : z ∈ S) : ∃ r : ℝ, 0 < r ∧
      Metric.ball z r ⊆ a ∧
      let P := Metric.ball z r ∩ {w | 0 < F w}
      let N := Metric.ball z r ∩ {w | F w < 0}
      P.Nonempty ∧ N.Nonempty ∧ Metric.ball z r \ S = P ∪ N ∧
      P ⊆ βp ∧ N ⊆ βn := by
    obtain ⟨rp, hrp, hp⟩ := hpnear z hz
    obtain ⟨rn, hrn, hn⟩ := hnnear z hz
    obtain ⟨r, hr, hball, hP, hN, hPc, hNc, hparts⟩ :=
      chord_local_half_disks hAB hz
        ((haOpen.inter Metric.isOpen_ball).inter Metric.isOpen_ball)
        (show z ∈ a ∩ Metric.ball z rp ∩ Metric.ball z rn from
          ⟨⟨hChord hz, Metric.mem_ball_self hrp⟩, Metric.mem_ball_self hrn⟩)
    refine ⟨r, hr, fun w hw ↦ (hball hw).1.1, hP, hN, hparts, ?_, ?_⟩
    · intro w hw
      exact hp ⟨(hball hw.1).1.2, hw.2⟩
    · intro w hw
      exact hn ⟨(hball hw.1).2, (show 0 < -F w from neg_pos.mpr hw.2)⟩
  let m := midpoint ℝ A B
  have hm : m ∈ S := midpoint_mem_openSegment A B
  obtain ⟨r, hr, hrball, hP, hN, hparts, hPβ, hNβ⟩ := hnear m hm
  obtain ⟨x, hxball, hxF⟩ := hP
  obtain ⟨xm, xp, hxm, hxp, hLxm, hLxp, hxne, hstubd, hmstub, hnp⟩ :=
    chord_transverse_stub L hm (sub_eq_zero.mp ((hFL m).symm.trans (hFzero m hm)))
      (sub_eq_zero.mp ((hFL B).symm.trans (hFseg B (right_mem_segment ℝ A B))))
      hxball (by change 0 < F x at hxF; rwa [hFL, sub_pos] at hxF)
  have hxpβ : xp ∈ βp := hPβ ⟨hxp, by change 0 < F xp; rw [hFL]; exact sub_pos.mpr hLxp⟩
  have hxmβ : xm ∈ βn := hNβ ⟨hxm, by change F xm < 0; rw [hFL]; exact sub_neg.mpr hLxm⟩
  have hstubA : segment ℝ xm xp ⊆ a :=
    ((convex_ball m r).segment_subset hxm hxp).trans hrball
  have hstubC : Disjoint (segment ℝ xm xp) (range c) :=
    disjoint_left.mpr (fun z hz hzc ↦ haSub (hstubA hz) hzc)
  have hsep : xp ∉ connectedComponentIn (range c ∪ segment ℝ A B)ᶜ xm :=
    cairns_marked_arc_separation (range c) hcurveCompact A B m xm xp hAB hm hxne
      hstubC hstubd hmstub hnp (c ∘ arc₁) (hc.continuous.comp hArc₁.continuous)
      (congrArg c hStart₁) (congrArg c hEnd₁) (by rintro z ⟨t, rfl⟩; exact ⟨arc₁ t, rfl⟩)
  have hVsub : V ⊆ (range c ∪ segment ℝ A B)ᶜ := by
    intro z hz hzc
    rcases hzc with hzc | hzd
    · exact haSub hz.1 hzc
    · exact (hremove ▸ (show z ∈ a \ openSegment ℝ (c p) (c q) from hz)).2 hzd
  have hβdis : Disjoint βp βn := by
    apply disjoint_left.mpr
    intro z hzp hzn
    have heq : βp = βn :=
      (connectedComponentIn_eq hzp).trans (connectedComponentIn_eq hzn).symm
    have hxpIn : xp ∈ connectedComponentIn V xm := by
      rw [← connectedComponentIn_eq hxmβ]
      change xp ∈ βn
      rw [← heq]
      exact hxpβ
    exact hsep (connectedComponentIn_mono xm hVsub hxpIn)
  have hSclosed : closure S ∩ a ⊆ S := by
    have hsegclosed : IsClosed (segment ℝ A B) := by
      rw [← convexHull_pair]
      exact ((Set.finite_singleton B).insert A).isCompact_convexHull ℝ |>.isClosed
    intro z hz
    have hzs : z ∈ segment ℝ A B := closure_minimal (openSegment_subset_segment ℝ A B)
      hsegclosed hz.1
    rw [← insert_endpoints_openSegment] at hzs
    rcases hzs with rfl | rfl | hzs
    · exact False.elim (haSub hz.2 ⟨p, rfl⟩)
    · exact False.elim (haSub hz.2 ⟨q, rfl⟩)
    · exact hzs
  have hcover : V = βp ∪ βn :=
    two_components_exhaust_of_local_cover haConnected.isPreconnected
      hβpo hβno hβps hβns hβpc.nonempty hSclosed
      (frontier_connectedComponentIn_subset_compl hcutOpen xp₀)
      (frontier_connectedComponentIn_subset_compl hcutOpen xn₀) (by
        intro z hz
        obtain ⟨r, hr, hball, hp, hn, heq, hpβ, hnβ⟩ := hnear z hz
        apply Filter.mem_of_superset (Metric.ball_mem_nhds z hr)
        intro w hw
        by_cases hwS : w ∈ S
        · exact Or.inr hwS
        · have := heq ▸ (show w ∈ Metric.ball z r \ S from ⟨hw, hwS⟩)
          exact Or.inl (this.elim (fun h ↦ Or.inl (hpβ h)) (fun h ↦ Or.inr (hnβ h))))
  let γ₁ : unitInterval → ℂ := c ∘ arc₁
  let γ₂ : unitInterval → ℂ := c ∘ arc₂
  have hγ₁ : Topology.IsEmbedding γ₁ := hc.comp hArc₁
  have hγ₂ : Topology.IsEmbedding γ₂ := hc.comp hArc₂
  have hγ₁0 : γ₁ 0 = A := congrArg c hStart₁
  have hγ₁1 : γ₁ 1 = B := congrArg c hEnd₁
  have hγ₂0 : γ₂ 0 = A := congrArg c hStart₂
  have hγ₂1 : γ₂ 1 = B := congrArg c hEnd₂
  have hγ₁C : range γ₁ ⊆ range c := by rintro z ⟨t, rfl⟩; exact ⟨arc₁ t, rfl⟩
  have hγ₂C : range γ₂ ⊆ range c := by rintro z ⟨t, rfl⟩; exact ⟨arc₂ t, rfl⟩
  have hγcover : range γ₁ ∪ range γ₂ = range c := by
    rw [show range γ₁ = c '' range arc₁ from range_comp _ _,
      show range γ₂ = c '' range arc₂ from range_comp _ _, ← image_union, hArcsCover, image_univ]
  have hγmeet : range γ₁ ∩ range γ₂ = {A, B} := by
    rw [show range γ₁ = c '' range arc₁ from range_comp _ _,
      show range γ₂ = c '' range arc₂ from range_comp _ _, ← image_inter hc.injective,
      hArcsMeet, image_pair]
  let T₁ := γ₁ '' Ioo 0 1
  let T₂ := γ₂ '' Ioo 0 1
  have hT₁c : IsPreconnected T₁ := isPreconnected_Ioo.image γ₁ hγ₁.continuous.continuousOn
  have hT₂c : IsPreconnected T₂ := isPreconnected_Ioo.image γ₂ hγ₂.continuous.continuousOn
  have hArcInterior (γ : unitInterval → ℂ) (hγ : Topology.IsEmbedding γ)
      (h0 : γ 0 = A) (h1 : γ 1 = B) (hγC : range γ ⊆ range c) :
      γ '' Ioo 0 1 ⊆ (segment ℝ A B)ᶜ ∧
      range γ \ segment ℝ A B ⊆ γ '' Ioo 0 1 := by
    have hnotEnds (t : unitInterval) (ht : t ∈ Ioo 0 1) : γ t ≠ A ∧ γ t ≠ B :=
      ⟨fun h ↦ ht.1.ne' (hγ.injective (h.trans h0.symm)),
        fun h ↦ ht.2.ne (hγ.injective (h.trans h1.symm))⟩
    constructor
    · rintro z ⟨t, ht, rfl⟩ hzd
      rw [← insert_endpoints_openSegment] at hzd
      rcases hzd with h | h | h
      · exact (hnotEnds t ht).1 h
      · exact (hnotEnds t ht).2 h
      · exact haSub (hChord h) (hγC ⟨t, rfl⟩)
    · rintro z ⟨⟨t, rfl⟩, hzd⟩
      refine ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr ?_, unitInterval.lt_one_iff_ne_one.mpr ?_⟩, rfl⟩
      · intro ht
        apply hzd
        rw [ht, h0]
        exact left_mem_segment ℝ A B
      · intro ht
        apply hzd
        rw [ht, h1]
        exact right_mem_segment ℝ A B
  obtain ⟨hT₁d, hArc₁T⟩ := hArcInterior γ₁ hγ₁ hγ₁0 hγ₁1 hγ₁C
  obtain ⟨hT₂d, hArc₂T⟩ := hArcInterior γ₂ hγ₂ hγ₂0 hγ₂1 hγ₂C
  have hT₁avoid : T₁ ⊆ (range γ₂ ∪ segment ℝ A B)ᶜ := by
    intro z hz hbad
    rcases hbad with hbad | hbad
    · have hends := hγmeet.subset ⟨image_subset_range _ _ hz, hbad⟩
      apply hT₁d hz
      rcases hends with rfl | h
      · exact left_mem_segment ℝ _ _
      · exact h ▸ right_mem_segment ℝ A B
    · exact hT₁d hz hbad
  have hT₂avoid : T₂ ⊆ (range γ₁ ∪ segment ℝ A B)ᶜ := by
    intro z hz hbad
    rcases hbad with hbad | hbad
    · have hends := hγmeet.subset ⟨hbad, image_subset_range _ _ hz⟩
      apply hT₂d hz
      rcases hends with rfl | h
      · exact left_mem_segment ℝ _ _
      · exact h ▸ right_mem_segment ℝ A B
    · exact hT₂d hz hbad
  have hnoBoth (γ : unitInterval → ℂ) (hγ : Continuous γ)
      (h0 : γ 0 = A) (h1 : γ 1 = B) (hγC : range γ ⊆ range c)
      (T : Set ℂ) (hT : IsPreconnected T)
      (hTU : T ⊆ (range γ ∪ segment ℝ A B)ᶜ) :
      ¬ ((frontier βp ∩ T).Nonempty ∧ (frontier βn ∩ T).Nonempty) := by
    rintro ⟨hcontactp, hcontactn⟩
    have hVγ : V ⊆ (range γ ∪ segment ℝ A B)ᶜ := by
      intro z hz hbad
      exact hVsub hz (hbad.elim (fun h ↦ Or.inl (hγC h)) Or.inr)
    have hconn := component_connection_of_frontier_contacts
      hβnc.isPreconnected hβpc.isPreconnected hT
      (hβns.trans hVγ) (hβps.trans hVγ) hTU hxmβ hxpβ hcontactn hcontactp
    exact cairns_marked_arc_separation (range γ) (isCompact_range hγ) A B m xm xp hAB hm hxne
      (hstubC.mono_right hγC) hstubd hmstub hnp γ hγ h0 h1 subset_rfl hconn
  have hno₁ := hnoBoth γ₂ hγ₂.continuous hγ₂0 hγ₂1 hγ₂C T₁ hT₁c hT₁avoid
  have hno₂ := hnoBoth γ₁ hγ₁.continuous hγ₁0 hγ₁1 hγ₁C T₂ hT₂c hT₂avoid
  obtain ⟨yp, hyp, hypF⟩ := positive_coordinate_frontier_point hβpo
    (haBounded.subset (hβps.trans sdiff_subset)) F hFcont hFopen hxpβ
    (by rw [hFL]; exact sub_pos.mpr hLxp)
  obtain ⟨yn, hyn, hynF⟩ := positive_coordinate_frontier_point hβno
    (haBounded.subset (hβns.trans sdiff_subset)) (fun w ↦ -F w) hFcont.neg
    ((Homeomorph.neg ℝ).isOpenMap.comp hFopen) hxmβ
    (by rw [hFL]; linarith)
  have hpointArc {z : ℂ} (hzC : z ∈ range c ∪ segment ℝ A B) (hzF : F z ≠ 0) :
      z ∈ T₁ ∪ T₂ := by
    have hzd : z ∉ segment ℝ A B := fun hz ↦ hzF (hFseg z hz)
    have hzC' : z ∈ range c := hzC.resolve_right hzd
    rw [← hγcover] at hzC'
    exact hzC'.elim (fun hz ↦ Or.inl (hArc₁T ⟨hz, hzd⟩))
      (fun hz ↦ Or.inr (hArc₂T ⟨hz, hzd⟩))
  have hypArc : yp ∈ T₁ ∪ T₂ := hpointArc (hcomponentFrontier xp₀ hyp) hypF.ne'
  have hynArc : yn ∈ T₁ ∪ T₂ := hpointArc (hcomponentFrontier xn₀ hyn) (ne_of_lt (neg_pos.mp hynF))
  have hfrontData (Bp Bn : Set ℂ)
      (hpf : frontier Bp ⊆ range c ∪ segment ℝ A B)
      (hnf : frontier Bn ⊆ range c ∪ segment ℝ A B)
      (hcontact : (frontier Bp ∩ T₁).Nonempty)
      (hother : (frontier Bn ∩ (T₁ ∪ T₂)).Nonempty)
      (hno1 : ¬ ((frontier Bp ∩ T₁).Nonempty ∧ (frontier Bn ∩ T₁).Nonempty))
      (hno2 : ¬ ((frontier Bp ∩ T₂).Nonempty ∧ (frontier Bn ∩ T₂).Nonempty)) :
      frontier Bp ⊆ segment ℝ A B ∪ range γ₁ ∧
      frontier Bn ⊆ segment ℝ A B ∪ range γ₂ := by
    have hn1 : ¬ (frontier Bn ∩ T₁).Nonempty := fun h ↦ hno1 ⟨hcontact, h⟩
    obtain ⟨w, hwf, hw⟩ := hother
    have hn2 : (frontier Bn ∩ T₂).Nonempty :=
      ⟨w, hwf, hw.resolve_left (fun h ↦ hn1 ⟨w, hwf, h⟩)⟩
    have hp2 : ¬ (frontier Bp ∩ T₂).Nonempty := fun h ↦ hno2 ⟨h, hn2⟩
    constructor
    · intro z hzf
      by_cases hzd : z ∈ segment ℝ A B
      · exact Or.inl hzd
      · right
        have hzC : z ∈ range γ₁ ∪ range γ₂ := hγcover.symm ▸ ((hpf hzf).resolve_right hzd)
        exact hzC.resolve_right (fun h ↦ hp2 ⟨z, hzf, hArc₂T ⟨h, hzd⟩⟩)
    · intro z hzf
      by_cases hzd : z ∈ segment ℝ A B
      · exact Or.inl hzd
      · right
        have hzC : z ∈ range γ₁ ∪ range γ₂ := hγcover.symm ▸ ((hnf hzf).resolve_right hzd)
        exact hzC.resolve_left (fun h ↦ hn1 ⟨z, hzf, hArc₁T ⟨h, hzd⟩⟩)
  have hcomponents (z : ℂ) (hz : z ∈ V) : connectedComponentIn V z = βp ∨
      connectedComponentIn V z = βn := by
    have hz' : z ∈ βp ∪ βn := hcover ▸ hz
    exact hz'.elim (fun h ↦ Or.inl (connectedComponentIn_eq h).symm)
      (fun h ↦ Or.inr (connectedComponentIn_eq h).symm)
  rcases hypArc with hyp₁ | hyp₂
  · obtain ⟨hpfront, hnfront⟩ := hfrontData βp βn (hcomponentFrontier xp₀)
      (hcomponentFrontier xn₀) ⟨yp, hyp, hyp₁⟩ ⟨yn, hyn, hynArc⟩ hno₁ hno₂
    refine ⟨βp, βn, hβpc.nonempty, hβnc.nonempty, hβpc, hβnc, hβpo, hβno,
      hβdis, hcover, hcomponents, ?_, ?_, ?_⟩
    · simpa only [γ₁, range_comp] using hpfront
    · simpa only [γ₂, range_comp] using hnfront
    · intro z hz
      obtain ⟨r, hr, hball, hP, hN, heq, hpβ, hnβ⟩ := hnear z hz
      exact ⟨r, hr, hball, hP, hN, heq, Or.inl ⟨hpβ, hnβ⟩⟩
  · have hyn₁ : yn ∈ T₁ := hynArc.resolve_right (fun h ↦ hno₂ ⟨⟨yp, hyp, hyp₂⟩, ⟨yn, hyn, h⟩⟩)
    obtain ⟨hnfront, hpfront⟩ := hfrontData βn βp (hcomponentFrontier xn₀)
      (hcomponentFrontier xp₀) ⟨yn, hyn, hyn₁⟩ ⟨yp, hyp, Or.inr hyp₂⟩
      (fun h ↦ hno₁ h.symm) (fun h ↦ hno₂ h.symm)
    refine ⟨βn, βp, hβnc.nonempty, hβpc.nonempty, hβnc, hβpc, hβno, hβpo,
      hβdis.symm, hcover.trans (union_comm _ _), ?_, ?_, ?_, ?_⟩
    · intro z hz; exact (hcomponents z hz).symm
    · simpa only [γ₁, range_comp] using hnfront
    · simpa only [γ₂, range_comp] using hpfront
    · intro z hz
      obtain ⟨r, hr, hball, hP, hN, heq, hpβ, hnβ⟩ := hnear z hz
      exact ⟨r, hr, hball, hP, hN, heq, Or.inr ⟨hpβ, hnβ⟩⟩

end HolomorphicAnosov

