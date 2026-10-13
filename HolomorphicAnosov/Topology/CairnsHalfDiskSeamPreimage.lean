import HolomorphicAnosov.Topology.CairnsHalfDiskBoundaryTransport

open Set Metric

namespace HolomorphicAnosov.Topology

/-- The diameter values of the half disk are exactly the affine image of the unit interval.
This is the elementary range calculation used to recover the seam from a half disk chart. -/
theorem cairns_diameter_range :
    range (fun t : unitInterval => ((2 * (t : ℝ) - 1 : ℝ) : ℂ)) = cairnsUnitDiameter := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    constructor
    · rw [mem_closedBall, dist_zero_right]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [t.property.1, t.property.2]
    · norm_num
  · intro hz
    let t : unitInterval :=
      ⟨((z : ℂ).re + 1) / 2, by
        have hz' := hz.1
        rw [mem_closedBall, dist_zero_right] at hz'
        have hr : |(z : ℂ).re| ≤ 1 := (Complex.abs_re_le_norm _).trans hz'
        rw [mem_Icc]
        constructor <;> nlinarith [neg_le_of_abs_le hr,
          le_abs_self (Complex.re (z : ℂ))]⟩
    refine ⟨t, ?_⟩
    apply Complex.ext
    · dsimp [t]
      nlinarith
    · have hz' : (z : ℂ).im = 0 := hz.2
      simpa using hz'.symm

/-- A half disk chart whose seam values are affine in the interval parameter has no
other preimages of the diameter. The forward seam equation, interval diameter range,
and injectivity of the chart suffice; no complementary boundary parametrization is used. -/
theorem cairns_halfdisk_seam_preimage
    (U B : Set ℂ) (H : closure U ≃ₜ cairnsClosedHalfDisk upper)
    (hc : B ⊆ closure U) (b : unitInterval → ℂ)
    (hrange : range b = B)
    (hB : ∀ t : unitInterval,
      ((H ⟨b t, hc (hrange ▸ mem_range_self t)⟩ : cairnsClosedHalfDisk upper) : ℂ) =
        ((2 * (t : ℝ) - 1 : ℝ) : ℂ)) :
    ∀ z : closure U, (H z : ℂ) ∈ cairnsUnitDiameter ↔ (z : ℂ) ∈ B := by
  intro z
  constructor
  · intro hz
    obtain ⟨t, ht⟩ := (Set.ext_iff.mp cairns_diameter_range (H z : ℂ)).mpr hz
    let zt : closure U := ⟨b t, hc (hrange ▸ mem_range_self t)⟩
    have hzt : (H z : ℂ) = (H zt : ℂ) := by
      calc
        (H z : ℂ) = ((2 * (t : ℝ) - 1 : ℝ) : ℂ) := ht.symm
        _ = (H zt : ℂ) := (hB t).symm
    have heq : z = zt := H.injective (Subtype.ext hzt)
    rw [heq]
    exact hrange ▸ mem_range_self t
  · intro hz
    obtain ⟨t, ht⟩ := hrange ▸ hz
    let zt : closure U := ⟨b t, hc (hrange ▸ mem_range_self t)⟩
    have heq : zt = z := by
      apply Subtype.ext
      exact ht
    rw [← heq]
    rw [hB]
    exact (Set.ext_iff.mp cairns_diameter_range _).mp ⟨t, rfl⟩

end HolomorphicAnosov.Topology

namespace HolomorphicAnosov.Topology

/-- The two half disk charts agree on the common seam when both use the same affine seam values. -/
theorem cairns_halfdisk_agree_on_seam
    (U₁ U₂ B : Set ℂ) (H₁ : closure U₁ ≃ₜ cairnsClosedHalfDisk true)
    (H₂ : closure U₂ ≃ₜ cairnsClosedHalfDisk false)
    (hc₁ : B ⊆ closure U₁) (hc₂ : B ⊆ closure U₂)
    (b : unitInterval → ℂ) (hrange : range b = B)
    (hB₁ : ∀ t : unitInterval,
      ((H₁ ⟨b t, hc₁ (hrange ▸ mem_range_self t)⟩ : cairnsClosedHalfDisk true) : ℂ) =
        ((2 * (t : ℝ) - 1 : ℝ) : ℂ))
    (hB₂ : ∀ t : unitInterval,
      ((H₂ ⟨b t, hc₂ (hrange ▸ mem_range_self t)⟩ : cairnsClosedHalfDisk false) : ℂ) =
        ((2 * (t : ℝ) - 1 : ℝ) : ℂ)) :
    ∀ z : B,
      (H₁ ⟨z, hc₁ z.property⟩ : ℂ) = (H₂ ⟨z, hc₂ z.property⟩ : ℂ) := by
  intro z
  have hzrange : (z : ℂ) ∈ range b := hrange ▸ z.property
  obtain ⟨t, ht⟩ := hzrange
  have hz₁ : (⟨b t, hc₁ (hrange ▸ mem_range_self t)⟩ : closure U₁) =
      ⟨z, hc₁ z.property⟩ := by
    apply Subtype.ext
    exact ht
  have hz₂ : (⟨b t, hc₂ (hrange ▸ mem_range_self t)⟩ : closure U₂) =
      ⟨z, hc₂ z.property⟩ := by
    apply Subtype.ext
    exact ht
  rw [← hz₁, ← hz₂, hB₁, hB₂]

/-- Equal values of the upper and lower half disk charts force both source points onto
 the common seam, then seam agreement and chart injectivity identify the source points. -/
theorem cairns_halfdisk_cross_injective
    (U₁ U₂ B : Set ℂ) (H₁ : closure U₁ ≃ₜ cairnsClosedHalfDisk true)
    (H₂ : closure U₂ ≃ₜ cairnsClosedHalfDisk false)
    (hc₁ : B ⊆ closure U₁) (hc₂ : B ⊆ closure U₂)
    (hpre₁ : ∀ z : closure U₁, (H₁ z : ℂ) ∈ cairnsUnitDiameter ↔ (z : ℂ) ∈ B)
    (hpre₂ : ∀ z : closure U₂, (H₂ z : ℂ) ∈ cairnsUnitDiameter ↔ (z : ℂ) ∈ B)
    (hagree : ∀ z : B,
      (H₁ ⟨z, hc₁ z.property⟩ : ℂ) = (H₂ ⟨z, hc₂ z.property⟩ : ℂ)) :
    ∀ x : closure U₁, ∀ y : closure U₂,
      (H₁ x : ℂ) = (H₂ y : ℂ) → (x : ℂ) = (y : ℂ) := by
  intro x y hxy
  have him₁ : 0 ≤ (H₁ x : ℂ).im := by
    have hx := (H₁ x).property
    simpa [cairnsClosedHalfDisk] using hx.2
  have him₂ : (H₂ y : ℂ).im ≤ 0 := by
    have hy := (H₂ y).property
    simpa [cairnsClosedHalfDisk] using hy.2
  have himzero : (H₁ x : ℂ).im = 0 := by
    apply le_antisymm
    · simpa [hxy] using him₂
    · exact him₁
  have hdiam₁ : (H₁ x : ℂ) ∈ cairnsUnitDiameter := by
    constructor
    · have hx := (H₁ x).property
      exact (by simpa [cairnsClosedHalfDisk] using hx.1)
    · exact himzero
  have hdiam₂ : (H₂ y : ℂ) ∈ cairnsUnitDiameter := by
    rw [← hxy]
    exact hdiam₁
  have hxB := (hpre₁ x).mp hdiam₁
  have hyB := (hpre₂ y).mp hdiam₂
  let xb : closure U₁ := ⟨(x : ℂ), hc₁ hxB⟩
  let yx : closure U₂ := ⟨(x : ℂ), hc₂ hxB⟩
  have hxy₁ : x = xb := by apply Subtype.ext; rfl
  have hag := hagree ⟨(x : ℂ), hxB⟩
  have hcharts : H₁ x = H₁ xb := by
    apply Subtype.ext
    rw [hxy₁]
  have hcharts' : H₂ y = H₂ yx := by
    apply Subtype.ext
    calc
      (H₂ y : ℂ) = (H₁ x : ℂ) := hxy.symm
      _ = (H₁ xb : ℂ) := congrArg Subtype.val hcharts
      _ = (H₂ yx : ℂ) := hag
  have hsource' : y = yx := H₂.injective hcharts'
  exact (congrArg Subtype.val hsource').symm

end HolomorphicAnosov.Topology
