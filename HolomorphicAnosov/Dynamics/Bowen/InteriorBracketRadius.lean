import HolomorphicAnosov.Dynamics.Bowen.CompactLocalProductData
import HolomorphicAnosov.Dynamics.Bowen.ProductChart
import HolomorphicAnosov.Dynamics.Bowen.FactOneNarrowBracketModulus
import HolomorphicAnosov.Dynamics.Bowen.FactOneProductScales

namespace HolomorphicAnosov.Dynamics.Bowen
open Set
open HolomorphicAnosov.BowenBasicSetCoding

/-- Interior bracket closure for sufficiently small bracket-closed sets.
Source: Bowen, Markov Partitions for Axiom A Diffeomorphisms (1970),
Lemmas 7–9 pp.729–730 and their use in Lemma 23 p.738.
No regular-closure or compactness hypothesis on the set is required.
DAG node: `dynamics.bowen_interior_bracket_radius_g17`.

Proof: choose a positive narrow-bracket modulus and Bowen's five scales, then
choose δ bounded by α₂/4, γ/4, ε/4 and εmod(γ/3)/4. Set
r=min(ε,εmod(δ)). For interior points x,y of a set of pair mesh at most r,
the projections u=[y,x] and q=[x,y] lie in the δ-plaques about x. The open
full-plaque collars of radius α₂/2 about x admit Bowen's product chart. Both
x and y belong to its image: [x,x]=x, and [[y,x],[x,y]]=y follows from
the γ/3 narrow bound and diagonal uniqueness, since γ/3+δ≤γ.

In this chart, the preimage of R is C×D, where C and D are the points of
R in the two chart factors. One direction uses bracket closure; the other
uses the inverse formulas ([z,x],[x,z]) and x∈R. Continuity takes the
interior points x,y into the interior of this product. The product-interior
identity shows that the unstable coordinate of x and stable coordinate of
y form another interior point. The chart followed by inclusion of its open
image is an open map, so this mixed point maps into interior R. Its image
is [x,[x,y]]=[x,y]; the last equality follows from bracket uniqueness,
q's stable plaque membership and the guard dist(x,q)≤δ≤ε. This proves the
claimed uniform interior-bracket property without any new assumption on R. -/
theorem exists_interior_bracket_radius
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (F : X ≃ₜ X) (γ lam : ℝ) (H : CompactLocalProductData F γ lam) :
    ∃ r : ℝ, 0 < r ∧ r ≤ H.closeRadius ∧
      ∀ R : Set X,
        (∀ x ∈ R, ∀ y ∈ R, dist x y ≤ r) →
        (∀ x ∈ R, ∀ y ∈ R, H.bracket x y ∈ R) →
        ∀ x ∈ interior R, ∀ y ∈ interior R,
          H.bracket x y ∈ interior R := by
  let ε := H.closeRadius
  let b := H.bracket
  have hγ := H.gamma_pos
  have hlam := H.lambda_pos
  have hlam1 := H.lambda_lt_one
  have hε := H.closeRadius_pos
  have hmem := H.bracket_mem
  have huniq := H.bracket_unique
  have hcont := H.bracket_continuous
  have hs := H.stable_contraction
  have hu := H.unstable_contraction
  classical
  have hm : ∀ δ : {δ : ℝ // 0 < δ}, ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∀ x y,
      dist x y ≤ η → b x y ∈ Dynamics.relativeClosedStablePlaque F δ.val x ∩
        Dynamics.relativeClosedUnstablePlaque F δ.val y := fun δ ↦
    factOne_narrow_bracket_modulus F γ lam ε hγ hlam.le hlam1.le hε
      b hmem huniq hcont hs hu δ.val δ.property
  choose η hη hηε hηmem using hm
  let εmod : ℝ → ℝ := fun δ ↦ if h : 0 < δ then η ⟨δ, h⟩ else ε
  have hmodpos : ∀ δ, 0 < δ → 0 < εmod δ := by
    intro δ hδ
    simpa only [εmod, dite_eq_left hδ] using hη ⟨δ, hδ⟩
  have hmod : ∀ δ, 0 < δ → δ ≤ γ → ∀ x y, dist x y ≤ εmod δ →
      b x y ∈ Dynamics.relativeClosedStablePlaque F δ x ∩
        Dynamics.relativeClosedUnstablePlaque F δ y := by
    intro δ hδ _ x y hxy
    exact hηmem ⟨δ, hδ⟩ x y (by simpa only [εmod, dite_eq_left hδ] using hxy)
  obtain ⟨α, hα0, hαpos, hαscale, hsmall⟩ :=
    exists_factOne_product_scales F γ hγ εmod hmodpos
  have hex : ∀ x y : X, dist x y ≤ ε → ∃! z,
      z ∈ Dynamics.relativeClosedStablePlaque F γ x ∧
        z ∈ Dynamics.relativeClosedUnstablePlaque F γ y := by
    intro x y hxy
    exact ⟨b x y, hmem x y hxy, fun z hz ↦ huniq x y z hxy hz⟩
  have hcharts := (HolomorphicAnosov.Bowen.bowen_fact1_product_chart_g6
    F lam γ ε hlam hlam1 hγ hε α εmod (fun δ hδ _ ↦ hmodpos δ hδ)
    hα0 hαpos hαscale hsmall b
    (fun x y z n hy hz ↦ hs x y z hy hz n)
    (fun x y z n hy hz ↦ hu x y z hy hz n) hex hmem hcont hmod).2
  let δ := min (α 2 / 4) (min (γ / 4) (min (ε / 4) (εmod (γ / 3) / 4)))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (div_pos (hαpos 2) (by norm_num)) (lt_min (by positivity)
      (lt_min (by positivity) (div_pos (hmodpos _ (by positivity)) (by norm_num))))
  have hδα : δ ≤ α 2 / 4 := min_le_left _ _
  have hδγ : δ ≤ γ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ ≤ ε / 4 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδmod : δ ≤ εmod (γ / 3) / 4 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  let r := min ε (εmod δ)
  have hr : 0 < r := lt_min hε (hmodpos δ hδ)
  refine ⟨r, hr, min_le_left _ _, ?_⟩
  intro R hsmall hR x hxi y hyi
  have hx : x ∈ R := interior_subset hxi
  have hy : y ∈ R := interior_subset hyi
  have hselfS (z : X) : z ∈ relativeClosedStablePlaque F γ z :=
    fun _ ↦ by simpa using hγ.le
  have hselfU (z : X) : z ∈ relativeClosedUnstablePlaque F γ z :=
    fun _ ↦ by simpa using hγ.le
  have hdiag (z : X) : b z z = z :=
    (huniq z z z (by simpa using hε.le) ⟨hselfS z, hselfU z⟩).symm
  have hxy := hsmall x hx y hy
  have hyx : dist y x ≤ r := by simpa only [dist_comm] using hxy
  have hq := hmod δ hδ (by linarith) x y (hxy.trans (min_le_right _ _))
  have hu := hmod δ hδ (by linarith) y x (hyx.trans (min_le_right _ _))
  let U : Set X := relativeClosedUnstablePlaque F γ x ∩ Metric.ball x (α 2 / 2)
  let V : Set X := relativeClosedStablePlaque F γ x ∩ Metric.ball x (α 2 / 2)
  have hU : U ⊆ relativeClosedUnstablePlaque F (α 2) x := by
    intro z hz n
    exact (H.unstable_contraction x z x hz.1 (hselfU x) n).trans
      ((mul_le_of_le_one_left dist_nonneg
        (pow_le_one₀ H.lambda_pos.le H.lambda_lt_one.le)).trans
        (by linarith [Metric.mem_ball.mp hz.2, hαpos 2]))
  have hV : V ⊆ relativeClosedStablePlaque F (α 2) x := by
    intro z hz n
    exact (H.stable_contraction x z x hz.1 (hselfS x) n).trans
      ((mul_le_of_le_one_left dist_nonneg
        (pow_le_one₀ H.lambda_pos.le H.lambda_lt_one.le)).trans
        (by linarith [Metric.mem_ball.mp hz.2, hαpos 2]))
  have hUo : IsOpen {u : relativeClosedUnstablePlaque F γ x | (u : X) ∈ U} := by
    have heq : {u : relativeClosedUnstablePlaque F γ x | (u : X) ∈ U} =
        Subtype.val ⁻¹' Metric.ball x (α 2 / 2) := by
      ext u
      exact and_iff_right u.property
    rw [heq]
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  have hVo : IsOpen {v : relativeClosedStablePlaque F γ x | (v : X) ∈ V} := by
    have heq : {v : relativeClosedStablePlaque F γ x | (v : X) ∈ V} =
        Subtype.val ⁻¹' Metric.ball x (α 2 / 2) := by
      ext v
      exact and_iff_right v.property
    rw [heq]
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  obtain ⟨hWo, hraw, hforwardraw, hinverseraw⟩ := hcharts x U V hU hV hUo hVo
  let W : Set X := {z | ∃ u ∈ U, ∃ v ∈ V, b u v = z}
  let T := {u : relativeClosedUnstablePlaque F γ x // (u : X) ∈ U}
  let S := {v : relativeClosedStablePlaque F γ x // (v : X) ∈ V}
  let h : (T × S) ≃ₜ W := hraw
  have hforward : ∀ p : T × S, (h p : X) = b p.1 p.2 := hforwardraw
  have hinverse : ∀ z : W, ((h.symm z).1 : X) = b z x ∧
      ((h.symm z).2 : X) = b x z := hinverseraw
  have hxU : x ∈ U := ⟨hselfU x, Metric.mem_ball.mpr (by simpa using half_pos (hαpos 2))⟩
  have hxV : x ∈ V := ⟨hselfS x, Metric.mem_ball.mpr (by simpa using half_pos (hαpos 2))⟩
  have huU : b y x ∈ U := ⟨fun n ↦ (hu.2 n).trans (by linarith),
    Metric.mem_ball.mpr (by have hh := hu.2 0; change dist (b y x) x ≤ δ at hh; linarith [hαpos 2])⟩
  have hqV : b x y ∈ V := ⟨fun n ↦ (hq.1 n).trans (by linarith),
    Metric.mem_ball.mpr (by have hh := hq.1 0; change dist (b x y) x ≤ δ at hh; linarith [hαpos 2])⟩
  have hpair : dist (b y x) (b x y) ≤ εmod (γ / 3) := by
    have hu0 := hu.2 0
    have hq0 := hq.1 0
    change dist (b y x) x ≤ δ at hu0
    change dist (b x y) x ≤ δ at hq0
    have ht := dist_triangle (b y x) x (b x y)
    rw [dist_comm x (b x y)] at ht
    linarith
  have hb := hmod (γ / 3) (by positivity) (by linarith) _ _ hpair
  have hreconstruct : b (b y x) (b x y) = y := by
    apply (huniq y y _ (by simpa using hε.le) ?_).trans (hdiag y)
    constructor
    · intro n
      exact (dist_triangle _ _ _).trans
        ((add_le_add (hb.1 n) (hu.1 n)).trans (by linarith))
    · intro n
      exact (dist_triangle _ _ _).trans
        ((add_le_add (hb.2 n) (hq.2 n)).trans (by linarith))
  have hxW : x ∈ W := ⟨x, hxU, x, hxV, hdiag x⟩
  have hyW : y ∈ W := ⟨b y x, huU, b x y, hqV, hreconstruct⟩
  let px := h.symm ⟨x, hxW⟩
  let py := h.symm ⟨y, hyW⟩
  let A := h ⁻¹' ((Subtype.val : W → X) ⁻¹' R)
  let C : Set {u : relativeClosedUnstablePlaque F γ x // (u : X) ∈ U} :=
    {u | (u : X) ∈ R}
  let D : Set {v : relativeClosedStablePlaque F γ x // (v : X) ∈ V} :=
    {v | (v : X) ∈ R}
  have hpre : A = C ×ˢ D := by
    ext p
    constructor
    · intro hp
      have hi := hinverse (h p)
      simp only [h.symm_apply_apply] at hi
      change (p.1 : X) ∈ R ∧ (p.2 : X) ∈ R
      rw [hi.1, hi.2]
      exact ⟨hR _ hp x hx, hR x hx _ hp⟩
    · intro hp
      change (h p : X) ∈ R
      rw [hforward]
      exact hR _ hp.1 _ hp.2
  have hcont' := continuous_subtype_val.comp h.continuous
  have hpx : px ∈ interior A := by
    apply preimage_interior_subset_interior_preimage hcont'
    change (h (h.symm ⟨x, hxW⟩) : X) ∈ interior R
    simpa only [Homeomorph.apply_symm_apply] using hxi
  have hpy : py ∈ interior A := by
    apply preimage_interior_subset_interior_preimage hcont'
    change (h (h.symm ⟨y, hyW⟩) : X) ∈ interior R
    simpa only [Homeomorph.apply_symm_apply] using hyi
  rw [hpre, interior_prod_eq] at hpx hpy
  have hmix : (px.1, py.2) ∈ interior A := by
    rw [hpre, interior_prod_eq]
    exact ⟨hpx.1, hpy.2⟩
  have hopen : IsOpenMap (fun p ↦ (h p : X)) :=
    hWo.isOpenEmbedding_subtypeVal.isOpenMap.comp h.isOpenMap
  have himem : (h (px.1, py.2) : X) ∈ interior R := by
    apply interior_mono (s := (fun p ↦ (h p : X)) '' A)
      (by rintro z ⟨p, hp, rfl⟩; exact hp)
    exact hopen.image_interior_subset A ⟨(px.1, py.2), hmix, rfl⟩
  have hpxval : (px.1 : X) = x := (hinverse ⟨x, hxW⟩).1.trans (hdiag x)
  have hpyval : (py.2 : X) = b x y := (hinverse ⟨y, hyW⟩).2
  rw [hforward, hpxval, hpyval] at himem
  have hqabsorb : b x (b x y) = b x y := by
    apply (huniq x (b x y) (b x y) ?_ ?_).symm
    · have hh := hq.1 0
      change dist (b x y) x ≤ δ at hh
      rw [dist_comm]
      linarith
    · exact ⟨fun n ↦ (hq.1 n).trans (by linarith), hselfU _⟩
  rwa [hqabsorb] at himem

end HolomorphicAnosov.Dynamics.Bowen
