import HolomorphicAnosov.Dynamics.Bowen.CompactLocalProductData
import HolomorphicAnosov.Dynamics.Bowen.ProductChart
import HolomorphicAnosov.Dynamics.Bowen.FactOneNarrowBracketModulus
import HolomorphicAnosov.Dynamics.Bowen.FactOneProductScales

noncomputable section

namespace HolomorphicAnosov.BowenBasicSetCoding

open Set Filter
open scoped Topology _root_.Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- The actual compact Fact 1 hypotheses supply all the qualitative canonical
coordinate data needed by the partition provider. Uniform modulus and scales
are constructed above; the existing Bowen product-chart theorem then gives
open images and a homeomorphism on the same full orbit-plaque subtypes.
Source: Bowen (1970), Fact 1 and Lemmas 5–8, pp. 727–729. -/
theorem compact_product_data_of_factOne
    [Nonempty X] (F : X ≃ₜ X) (γ lam ε : ℝ)
    (hγ : 0 < γ) (hlam : 0 < lam) (hlam1 : lam < 1) (hε : 0 < ε)
    (b : X → X → X)
    (hmem : ∀ x y, dist x y ≤ ε →
      b x y ∈ Dynamics.relativeClosedStablePlaque F γ x ∩
        Dynamics.relativeClosedUnstablePlaque F γ y)
    (huniq : ∀ x y z, dist x y ≤ ε →
      z ∈ Dynamics.relativeClosedStablePlaque F γ x ∩
        Dynamics.relativeClosedUnstablePlaque F γ y → z = b x y)
    (hcont : ContinuousOn (fun p : X × X ↦ b p.1 p.2) {p | dist p.1 p.2 ≤ ε})
    (hs : ∀ x y z, y ∈ Dynamics.relativeClosedStablePlaque F γ x →
      z ∈ Dynamics.relativeClosedStablePlaque F γ x → ∀ n : ℕ,
      dist ((F : X → X)^[n] y) ((F : X → X)^[n] z) ≤ lam ^ n * dist y z)
    (hu : ∀ x y z, y ∈ Dynamics.relativeClosedUnstablePlaque F γ x →
      z ∈ Dynamics.relativeClosedUnstablePlaque F γ x → ∀ n : ℕ,
      dist ((F.symm : X → X)^[n] y) ((F.symm : X → X)^[n] z) ≤ lam ^ n * dist y z) :
    Nonempty (Dynamics.Bowen.CompactLocalProductData F γ lam) := by
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
  refine ⟨{
    gamma_pos := hγ
    lambda_pos := hlam
    lambda_lt_one := hlam1
    stable_contraction := hs
    unstable_contraction := hu
    closeRadius := ε
    closeRadius_pos := hε
    bracket := b
    bracket_mem := hmem
    bracket_unique := huniq
    bracket_continuous := hcont
    product_chart := ?_ }⟩
  intro x
  let ρ := min (α 2) (ε / 2)
  refine ⟨ρ, lt_min (hαpos 2) (half_pos hε), (min_le_left _ _).trans hα2.le,
    by dsimp [ρ]; linarith [min_le_right (α 2) (ε / 2)], ?_⟩
  intro U V hU hV hUopen hVopen
  obtain ⟨hopen, h, hh, _⟩ := hcharts x U V
    (fun z hz n ↦ (hU hz n).trans (min_le_left _ _))
    (fun z hz n ↦ (hV hz n).trans (min_le_left _ _)) hUopen hVopen
  exact ⟨hopen, h, hh⟩


end HolomorphicAnosov.BowenBasicSetCoding
