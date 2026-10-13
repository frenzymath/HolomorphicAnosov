import HolomorphicAnosov.Analysis.MarkedRectangleG3DiskSchwarzChristoffel
import HolomorphicAnosov.Topology.CairnsCrosscutAmbientTransport
import HolomorphicAnosov.Analysis.QCSignedDistortionModulusRectangleConformalModel
import Mathlib.Analysis.Convex.GaugeRescale

/-! # Alternating opposite-corner crosscuts intersect

Source: Cairns, An Elementary Proof of the Jordan–Schoenflies Theorem (1951),
Lemma 5.1, printed p.866, following Theorem 4.1. The precise rectangle
specialization is the remaining semantic audit obligation for QCPartition.
-/

namespace HolomorphicAnosov
open Set Metric Bornology
open Analysis.MarkedRectangle
open scoped Pointwise _root_.Topology ComplexConjugate

/-- A connected open-arc image cannot be covered by two disjoint open
component sides when its endpoints lie outside the opposite side closures.
This is the endpoint-continuity step used after the Cairns crosscut theorem.
Source: Cairns (1951), Lemma 5.1 p.866. -/
lemma qc_crossing_endpoint_component_contradiction
    (β : unitInterval → ℂ) (hβ : Continuous β)
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) (hd : Disjoint U V)
    (hcover : β '' Ioo 0 1 ⊆ U ∪ V)
    (h₀ : β 0 ∉ closure V) (h₁ : β 1 ∉ closure U) : False := by
  have hc : IsPreconnected (β '' Ioo 0 1) :=
    isPreconnected_Ioo.image β hβ.continuousOn
  have hcl : closure (Ioo (0 : unitInterval) 1) = univ := by
    rw [closure_Ioo (show (0 : unitInterval) ≠ 1 by norm_num)]
    exact Set.Icc_bot_top
  have hend (t : unitInterval) : β t ∈ closure (β '' Ioo 0 1) := by
    apply image_closure_subset_closure_image hβ
    exact ⟨t, hcl.symm ▸ mem_univ t, rfl⟩
  rcases hc.subset_or_subset hU hV hd hcover with h | h
  · exact h₁ (closure_mono h (hend 1))
  · exact h₀ (closure_mono h (hend 0))

/-- Two embedded arcs in a positive closed rectangle joining alternate corners,
with their open arcs in the open rectangle, meet at interior parameters.

Source: Cairns (1951), Lemma 5.1, p.866; local text
`literature/cairns-jordan-schoenflies-1951.txt`, lines 298–312.

Proof: the closed rectangle is a topological disk. Apply the crosscut theorem
(Cairns 5.1, transported by a disk chart) to α. The complement of its open arc
in the open rectangle has exactly two open connected components. Their
frontiers consist of the full α arc together with the two boundary arcs from
0 to M+i. The corners M and i lie on different open boundary arcs.
If the full β arc missed α, its connected open arc would be contained in one
of these components. Both β endpoints lie in the closure of that component
by continuity and density of (0,1) in [0,1]. Its frontier description cannot
contain both M and i: neither is on α, and the component's one boundary arc
contains exactly one of them. This contradiction yields an intersection.
All intersections have interior parameters: the four endpoints are distinct
when M>0, and an open-arc point belongs to the open rectangle, whereas each
endpoint is on the boundary. This proof uses no regularity of either arc and
no modulus, measure, or saturation assumption.

Formal residual: instantiate the ambient disk chart and transport the two
boundary-arc labels in `cairns_crosscut_ambient_transport`; then apply the
connected-component and endpoint closure argument above. -/
theorem qc_rectangle_opposite_corner_crossing
    {M : ℝ} (hM : 0 < M) (α β : unitInterval → ℂ)
    (hα : Topology.IsEmbedding α) (hβ : Topology.IsEmbedding β)
    (hα0 : α 0 = 0) (hα1 : α 1 = (M : ℂ) + Complex.I)
    (hβ0 : β 0 = (M : ℂ)) (hβ1 : β 1 = Complex.I)
    (hclosed : ∀ t, α t ∈ ClosedRectangle M 1 ∧ β t ∈ ClosedRectangle M 1)
    (hopen : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
      α t ∈ OpenRectangle M 1 ∧ β t ∈ OpenRectangle M 1) :
    ∃ s t : unitInterval, 0 < (s : ℝ) ∧ (s : ℝ) < 1 ∧
      0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ α s = β t := by
  let c₀ : ℂ := (M / 2 : ℝ) + (1 / 2 : ℝ) * Complex.I
  let s₀ : Set ℂ := (-c₀) +ᵥ OpenRectangle M 1
  have hsconv : Convex ℝ s₀ := by
    apply Convex.vadd
    change Convex ℝ (Complex.equivRealProdLm.toLinearMap ⁻¹' (Ioo 0 M ×ˢ Ioo 0 1))
    exact ((convex_Ioo (0 : ℝ) M).prod (convex_Ioo (0 : ℝ) 1)).linear_preimage
      Complex.equivRealProdLm.toLinearMap
  have hsopen : IsOpen s₀ := (RectangleModelPreparation.isOpen_openRectangle M 1).vadd (-c₀)
  have hsmem : (0 : ℂ) ∈ s₀ := by
    refine ⟨c₀, ?_, neg_add_cancel c₀⟩
    dsimp [c₀]
    simp only [OpenRectangle, Complex.mem_reProdIm, mem_Ioo, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, mul_one, zero_add]
    constructor <;> constructor <;> linarith
  have hs0 : s₀ ∈ 𝓝 (0 : ℂ) := hsopen.mem_nhds hsmem
  have hsb : IsBounded s₀ :=
    ((isBounded_Ioo 0 M).reProdIm (isBounded_Ioo 0 1)).vadd (-c₀)
  have htb : IsVonNBounded ℝ (ball (0 : ℂ) 1) := NormedSpace.isVonNBounded_ball ℝ ℂ 1
  have hst : IsVonNBounded ℝ s₀ := NormedSpace.isVonNBounded_of_isBounded ℝ hsb
  have ht0 : ball (0 : ℂ) 1 ∈ 𝓝 0 := isOpen_ball.mem_nhds (by simp)
  let e := gaugeRescaleHomeomorph s₀ (ball (0 : ℂ) 1) hsconv hs0 hst
    (convex_ball 0 1) ht0 htb
  let H : ℂ ≃ₜ ℂ := (Homeomorph.addLeft (-c₀)).trans e
  have hH : H '' OpenRectangle M 1 = ball (0 : ℂ) 1 := by
    change (fun z ↦ e (-c₀ + z)) '' OpenRectangle M 1 = _
    rw [← Set.image_image]
    change e '' s₀ = _
    rw [← hsopen.interior_eq]
    exact (image_gaugeRescaleHomeomorph_interior hsconv hs0 hst
      (convex_ball 0 1) ht0 htb).trans isOpen_ball.interior_eq
  have hHcl : H '' ClosedRectangle M 1 = closedBall (0 : ℂ) 1 := by
    rw [← RectangleModelPreparation.closure_openRectangle hM zero_lt_one, H.image_closure, hH,
      closure_ball (0 : ℂ) one_ne_zero]
  have hrad (z : ℂ) (hz : z ≠ c₀) : ∃ r : ℝ, 0 < r ∧ H z = r • (z - c₀) := by
    have hne : -c₀ + z ≠ 0 := by
      have hz' : z - c₀ ≠ 0 := sub_ne_zero.mpr hz
      simpa [sub_eq_add_neg, add_comm] using hz'
    refine ⟨gauge s₀ (-c₀ + z) / gauge (ball (0 : ℂ) 1) (-c₀ + z),
      div_pos ((gauge_pos (absorbent_nhds_zero hs0) hst).mpr hne)
        ((gauge_pos (absorbent_nhds_zero ht0) htb).mpr hne), ?_⟩
    change gaugeRescale s₀ (ball (0 : ℂ) 1) (-c₀ + z) = _
    simp only [gaugeRescale, neg_add_eq_sub]
  have hcornerS (z : ℂ) (hz : z ∈ ClosedRectangle M 1)
      (hznot : z ∉ OpenRectangle M 1) : H z ∈ sphere (0 : ℂ) 1 := by
    have hzcl : H z ∈ closedBall (0 : ℂ) 1 := hHcl ▸ ⟨z, hz, rfl⟩
    have hznob : H z ∉ ball (0 : ℂ) 1 := by
      intro hb
      obtain ⟨w, hw, heq⟩ := hH.symm ▸ hb
      exact hznot (H.injective heq ▸ hw)
    rw [← closedBall_sdiff_ball]
    exact ⟨hzcl, hznob⟩
  let c : Set ℂ := H ⁻¹' sphere (0 : ℂ) 1
  let η : unitInterval → closure (OpenRectangle M 1) := fun u ↦
    ⟨α u, by rw [RectangleModelPreparation.closure_openRectangle hM zero_lt_one]
             exact (hclosed u).1⟩
  have hη : _root_.Topology.IsEmbedding η := hα.codRestrict _ _
  have hη0 : (η 0 : ℂ) ∈ c := by
    change H (α 0) ∈ sphere (0 : ℂ) 1
    rw [hα0]
    exact hcornerS 0 (by simp [ClosedRectangle, Complex.reProdIm, hM.le])
      (by simp [OpenRectangle, Complex.reProdIm])
  have hη1 : (η 1 : ℂ) ∈ c := by
    change H (α 1) ∈ sphere (0 : ℂ) 1
    rw [hα1]
    exact hcornerS ((M : ℂ) + Complex.I)
      (by simp [ClosedRectangle, Complex.reProdIm, hM.le])
      (by simp [OpenRectangle, Complex.reProdIm])
  have hη01 : η 0 ≠ η 1 := by
    intro heq
    have h01 := hα.injective (congrArg Subtype.val heq)
    exact zero_ne_one h01
  have hinterior (u : unitInterval) (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1) :
      (η u : ℂ) ∈ OpenRectangle M 1 := (hopen u hu0 hu1).1
  obtain ⟨V, hV, hdis, hcover, hcomp, hfront⟩ :=
    cairns_crosscut_ambient_transport H (OpenRectangle M 1) c hH
      (H.surjective.image_preimage _) η hη hη0 hη1 hη01 hinterior
  let I : Set unitInterval := {u | 0 < (u : ℝ) ∧ (u : ℝ) < 1}
  have hI : I = Ioo (0 : unitInterval) 1 := rfl
  let K : Set ℂ := range α
  let Kopen : Set ℂ := α '' I
  let Ω : Set ℂ := OpenRectangle M 1 \ Kopen
  change (⋃ i, V i) = Ω at hcover
  change ∀ i, frontier (V i) = K ∪ {z | z ∈ c ∧ if i = 0 then
    (conj (H (α 1) - H (α 0)) * (H z - H (α 0))).im ≤ 0
    else 0 ≤ (conj (H (α 1) - H (α 0)) * (H z - H (α 0))).im} at hfront
  have hVsub (i : Fin 2) : V i ⊆ OpenRectangle M 1 := by
    intro z hz
    have : z ∈ Ω := hcover ▸ mem_iUnion.mpr ⟨i, hz⟩
    exact this.1
  have hβbd0 : β 0 ∉ OpenRectangle M 1 := by
    rw [hβ0]; simp [OpenRectangle, Complex.reProdIm]
  have hβbd1 : β 1 ∉ OpenRectangle M 1 := by
    rw [hβ1]; simp [OpenRectangle, Complex.reProdIm]
  have hαcontacts (u : unitInterval) (hu : α u ∉ OpenRectangle M 1) : u = 0 ∨ u = 1 := by
    by_cases h0 : u = 0
    · exact Or.inl h0
    by_cases h1 : u = 1
    · exact Or.inr h1
    have hu0 : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1
      (fun h ↦ h0 (Subtype.ext h.symm))
    have hu1 : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2
      (fun h ↦ h1 (Subtype.ext h))
    exact (hu (hopen u hu0 hu1).1).elim
  have hβ0K : β 0 ∉ K := by
    rintro ⟨u, hu⟩
    rcases hαcontacts u (hu.symm ▸ hβbd0) with rfl | rfl
    · rw [hα0, hβ0] at hu
      have hr := congrArg Complex.re hu
      simp at hr
      linarith
    · rw [hα1, hβ0] at hu
      have hi := congrArg Complex.im hu
      norm_num at hi
  have hβ1K : β 1 ∉ K := by
    rintro ⟨u, hu⟩
    rcases hαcontacts u (hu.symm ▸ hβbd1) with rfl | rfl
    · rw [hα0, hβ1] at hu
      have hi := congrArg Complex.im hu
      norm_num at hi
    · rw [hα1, hβ1] at hu
      have hr := congrArg Complex.re hu
      simp at hr
      linarith
  by_contra hno
  have hβsub : β '' I ⊆ Ω := by
    rintro z ⟨u, hu, rfl⟩
    refine ⟨(hopen u hu.1 hu.2).2, ?_⟩
    rintro ⟨v, hv, heq⟩
    exact hno ⟨v, u, hv.1, hv.2, hu.1, hu.2, heq⟩
  have hconn : IsPreconnected (β '' I) := by
    rw [hI]
    exact isPreconnected_Ioo.image β hβ.continuous.continuousOn
  have hside : ∃ i : Fin 2, β '' I ⊆ V i := by
    have hsub : β '' I ⊆ V 0 ∪ V 1 := by
      intro z hz
      have hz' : z ∈ ⋃ j, V j := hcover ▸ hβsub hz
      obtain ⟨j, hj⟩ := mem_iUnion.mp hz'
      fin_cases j
      · exact Or.inl hj
      · exact Or.inr hj
    rcases hconn.subset_or_subset (hV 0).2.1 (hV 1).2.1 hdis hsub with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hside
  have hend (u : unitInterval) : β u ∈ closure (β '' I) := by
    apply image_closure_subset_closure_image hβ.continuous
    refine ⟨u, ?_, rfl⟩
    rw [hI, closure_Ioo (show (0 : unitInterval) ≠ 1 by norm_num)]
    exact u.property
  have hβcl (u : unitInterval) : β u ∈ closure (V i) := closure_mono hi (hend u)
  have hfront0 : β 0 ∈ frontier (V i) := by
    rw [(hV i).2.1.frontier_eq]
    exact ⟨hβcl 0, fun hz ↦ hβbd0 (hVsub i hz)⟩
  have hfront1 : β 1 ∈ frontier (V i) := by
    rw [(hV i).2.1.frontier_eq]
    exact ⟨hβcl 1, fun hz ↦ hβbd1 (hVsub i hz)⟩
  rw [hfront i] at hfront0 hfront1
  have hA0 := (hfront0.resolve_left hβ0K).2
  have hA1 := (hfront1.resolve_left hβ1K).2
  rw [hα0, hα1, hβ0] at hA0
  rw [hα0, hα1, hβ1] at hA1
  have hsign0 : (conj (H ((M : ℂ) + Complex.I) - H 0) * (H (M : ℂ) - H 0)).im < 0 := by
    obtain ⟨r0,hr0,h0⟩ := hrad 0 (by intro h; have := congrArg Complex.im h; norm_num [c₀] at this)
    obtain ⟨r1,hr1,h1⟩ := hrad ((M : ℂ) + Complex.I) (by intro h; have := congrArg Complex.im h; norm_num [c₀] at this)
    obtain ⟨rM,hrM,hM'⟩ := hrad (M : ℂ) (by intro h; have := congrArg Complex.im h; norm_num [c₀] at this)
    rw [h0,h1,hM']
    dsimp [c₀]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.zero_re, Complex.zero_im, Complex.mul_re]
    nlinarith [mul_pos (mul_pos hM (add_pos hr0 hr1)) hrM]
  have hsign1 : 0 < (conj (H ((M : ℂ) + Complex.I) - H 0) * (H Complex.I - H 0)).im := by
    obtain ⟨r0,hr0,h0⟩ := hrad 0 (by intro h; have := congrArg Complex.im h; norm_num [c₀] at this)
    obtain ⟨r1,hr1,h1⟩ := hrad ((M : ℂ) + Complex.I) (by intro h; have := congrArg Complex.im h; norm_num [c₀] at this)
    obtain ⟨rI,hrI,hI⟩ := hrad Complex.I (by intro h; have := congrArg Complex.im h; norm_num [c₀] at this)
    rw [h0,h1,hI]
    dsimp [c₀]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.zero_re, Complex.zero_im, Complex.mul_re]
    nlinarith [mul_pos (mul_pos hM (add_pos hr0 hr1)) hrI]
  fin_cases i
  · exact (not_le_of_gt hsign1) (by simpa using hA1)
  · exact (not_le_of_gt hsign0) (by simpa using hA0)


end HolomorphicAnosov

