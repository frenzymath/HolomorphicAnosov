import HolomorphicAnosov.Dynamics.Bowen.CompactLocalProductData
import HolomorphicAnosov.Dynamics.Bowen.ProductChart
import HolomorphicAnosov.Dynamics.Bowen.FactOneNarrowBracketModulus
import HolomorphicAnosov.Dynamics.Bowen.FactOneProductScales
import HolomorphicAnosov.Topology.ManningBowenInitialCoverUniformSaturation

namespace HolomorphicAnosov.Dynamics.Bowen
open Set
open HolomorphicAnosov.BowenBasicSetCoding

/-- Bowen Fact 1 and Lemmas 5–8, pp.727–729: uniform small chart radius
and strict-domain canonical coordinates from compact contracting bracket data.
The bracket remains the restriction of the given total representative.

Proof: the compact narrow-bracket modulus and Bowen's descending-scale choice
supply positive scales α₀,...,α₄. The product-chart theorem gives open products
at the uniform radius α₂. Set r = min(α₂, ε/4), where ε is the original bracket
domain radius. Then r > 0, r < γ and r < ε/3. Each pair of factors in the r
plaques has distance at most 2r < ε, so restricting the total bracket to the
strict pair domain preserves its product image. The chart's nested plaque
subtypes are homeomorphic to the factors themselves, since the factors lie in
the full plaques. Composing these homeomorphisms gives the required chart.
Symmetry of distance identifies the two plaque conventions. Restriction of the
original continuous bracket gives strict-domain continuity, and its membership
and uniqueness give the singleton-intersection identity. -/
theorem canonicalCoordinatesOfCompactData
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (F : X ≃ₜ X) (γ lam : ℝ) (H : CompactLocalProductData F γ lam) :
    ∃ K : ManningBowenCanonicalCoordinates F γ lam H.closeRadius,
      ∀ p, K.bracket p = H.bracket p.val.1 p.val.2 := by
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
  have hα1 : α 1 < γ := by
    have h := (hαscale 0).trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero, hα0] at h
    linarith
  have hα2 : α 2 < γ := by
    have h := (hαscale 1).trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    norm_num at h
    linarith [hαpos 1]
  have eqS (r : ℝ) (x : X) : manningBowenStablePlaque F r x =
      relativeClosedStablePlaque F r x := by
    ext y
    simp only [manningBowenStablePlaque, relativeClosedStablePlaque, mem_ofPred_eq, dist_comm]
  have eqU (r : ℝ) (x : X) : manningBowenUnstablePlaque F r x =
      relativeClosedUnstablePlaque F r x := by
    ext y
    simp only [manningBowenUnstablePlaque, relativeClosedUnstablePlaque, mem_ofPred_eq, dist_comm]
  let pb : manningBowenPairDomain (X := X) ε → X := fun p ↦ b p.val.1 p.val.2
  have hpb : Continuous pb := by
    have hc : ContinuousOn (fun p : X × X ↦ b p.1 p.2) {p | dist p.1 p.2 < ε} :=
      hcont.mono (fun p hp ↦ (show dist p.1 p.2 < ε from hp).le)
    exact continuousOn_iff_continuous_domRestrict.mp hc
  let r := min (α 2) (ε / 4)
  have hr : 0 < r := lt_min (hαpos 2) (by positivity)
  have hrα : r ≤ α 2 := min_le_left _ _
  have hrε : r < ε / 3 := (min_le_right _ _).trans_lt (by dsimp [ε]; linarith)
  have hrg : r < γ := hrα.trans_lt hα2
  have hprod : ∀ (x : X) (U V : Set X),
      U ⊆ manningBowenUnstablePlaque F γ x → V ⊆ manningBowenStablePlaque F γ x →
      IsOpen (Subtype.val ⁻¹' U : Set (manningBowenUnstablePlaque F γ x)) →
      IsOpen (Subtype.val ⁻¹' V : Set (manningBowenStablePlaque F γ x)) →
      U ⊆ manningBowenUnstablePlaque F r x → V ⊆ manningBowenStablePlaque F r x →
      IsOpen (manningBowenBracketImage pb U V) ∧
        ∃ h : (U × V) ≃ₜ manningBowenBracketImage pb U V,
          ∀ p : U × V, ∀ hp : dist (p.1 : X) (p.2 : X) < ε,
            (h p : X) = pb ⟨((p.1 : X), (p.2 : X)), hp⟩ := by
    intro x U V hUg hVg hUo hVo hUr hVr
    have hUo' : IsOpen {u : relativeClosedUnstablePlaque F γ x | (u : X) ∈ U} :=
      hUo.preimage (Homeomorph.setCongr (eqU γ x)).symm.continuous
    have hVo' : IsOpen {v : relativeClosedStablePlaque F γ x | (v : X) ∈ V} :=
      hVo.preimage (Homeomorph.setCongr (eqS γ x)).symm.continuous
    simp only [eqU, eqS] at hUg hVg hUr hVr
    obtain ⟨hopen, h, hh, _⟩ := hcharts x U V
      (fun z hz n ↦ (hUr hz n).trans hrα)
      (fun z hz n ↦ (hVr hz n).trans hrα) hUo' hVo'
    have hpair (u : U) (v : V) : dist (u : X) (v : X) < ε := by
      have hu0 := hUr u.property 0
      have hv0 := hVr v.property 0
      simp only [Function.iterate_zero, id_eq] at hu0 hv0
      calc
        dist (u : X) (v : X) ≤ dist (u : X) x + dist x (v : X) := dist_triangle _ _ _
        _ ≤ r + r := add_le_add hu0 (by simpa only [dist_comm] using hv0)
        _ < ε := by linarith
    have himage : manningBowenBracketImage pb U V =
        {z | ∃ u ∈ U, ∃ v ∈ V, b u v = z} := by
      ext z
      constructor
      · rintro ⟨p, hpU, hpV, hp⟩
        exact ⟨p.val.1, hpU, p.val.2, hpV, hp⟩
      · rintro ⟨u, hu, v, hv, heq⟩
        exact ⟨⟨(u,v), hpair ⟨u,hu⟩ ⟨v,hv⟩⟩, hu, hv, heq⟩
    let eu : U ≃ₜ {u : relativeClosedUnstablePlaque F γ x // (u : X) ∈ U} := {
      toFun := fun u ↦ ⟨⟨u.val, hUg u.property⟩, u.property⟩
      invFun := fun u ↦ ⟨u.val.val, u.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
    let ev : V ≃ₜ {v : relativeClosedStablePlaque F γ x // (v : X) ∈ V} := {
      toFun := fun v ↦ ⟨⟨v.val, hVg v.property⟩, v.property⟩
      invFun := fun v ↦ ⟨v.val.val, v.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
    refine ⟨himage.symm ▸ hopen, ⟨((eu.prodCongr ev).trans h).trans (Homeomorph.setCongr himage.symm), ?_⟩⟩
    intro p hp
    exact hh (eu p.1, ev p.2)
  refine ⟨{
    gamma_pos := hγ
    rate_pos := hlam
    rate_lt_one := hlam1
    epsilon_pos := hε
    stable_contraction := ?_
    unstable_contraction := ?_
    bracket := pb
    bracket_continuous := hpb
    bracket_intersection := ?_
    productRadius := r
    productRadius_pos := hr
    productRadius_lt_gamma := hrg
    productRadius_lt_epsilon := hrε
    local_product := hprod }, ?_⟩
  · intro x y hy z hz n
    rw [eqS] at hy hz
    exact hs x y z hy hz n
  · intro x y hy z hz n
    rw [eqU] at hy hz
    exact hu x y z hy hz n
  · intro p
    rw [eqS, eqU]
    ext z
    constructor
    · intro hz
      exact Set.mem_singleton_iff.mpr (huniq p.val.1 p.val.2 z p.property.le hz)
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hmem p.val.1 p.val.2 p.property.le
  · intro p
    rfl

end HolomorphicAnosov.Dynamics.Bowen
