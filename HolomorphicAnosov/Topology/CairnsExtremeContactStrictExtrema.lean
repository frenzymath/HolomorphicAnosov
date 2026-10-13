import HolomorphicAnosov.Topology.WhyburnCircleSplit

open Set Metric

namespace HolomorphicAnosov

/-- An embedded circle cannot have constant imaginary coordinate. -/
theorem cairns_embedded_circle_ordinate_nonconstant
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ) (c : ℝ)
    (hconst : ∀ z ∈ Set.range γ, z.im = c) : False := by
  let a : ℂ := γ 1
  let b : ℂ := γ (-1)
  have ha : a ∈ Set.range γ := ⟨1, rfl⟩
  have hb : b ∈ Set.range γ := ⟨-1, rfl⟩
  have hab : a ≠ b := by
    intro hab
    have hdom : (1 : Circle) = -1 := hγ.injective (by simpa [a, b] using hab)
    have hcoe := congrArg (fun z : Circle => (z : ℂ)) hdom
    norm_num at hcoe
  have him : a.im = b.im := by rw [hconst a ha, hconst b hb]
  have hres : a.re ≠ b.re := by
    intro hre
    apply hab
    exact Complex.ext hre him
  obtain hlt | hgt := lt_or_gt_of_ne hres
  · obtain ⟨u, v, hu, hv, huv, e₂, e₃, he₂, he₃, h0₂, h1₂, h0₃, h1₃, hun, hinter⟩ :=
      Topology.circle_split_two_arcs γ hγ a b ha hb hab
    have hc₂ : Continuous (fun t : unitInterval ↦ (e₂ t).re) :=
      Complex.continuous_re.comp (he₂.continuous)
    have hc₃ : Continuous (fun t : unitInterval ↦ (e₃ t).re) :=
      Complex.continuous_re.comp (he₃.continuous)
    let r : ℝ := (a.re + b.re) / 2
    have hra : a.re ≤ r := by dsimp [r]; linarith
    have hrb : r ≤ b.re := by dsimp [r]; linarith
    obtain ⟨t, ht⟩ := (intermediate_value_univ (0 : unitInterval) (1 : unitInterval) hc₂)
      ⟨by simpa [h0₂] using hra, by simpa [h1₂] using hrb⟩
    obtain ⟨s, hs⟩ := (intermediate_value_univ (1 : unitInterval) (0 : unitInterval) hc₃)
      ⟨by simpa [h1₃] using hra, by simpa [h0₃] using hrb⟩
    have htγ : e₂ t ∈ Set.range γ := by
      rw [← hun]
      exact mem_union_left _ ⟨t, rfl⟩
    have hsγ : e₃ s ∈ Set.range γ := by
      rw [← hun]
      exact mem_union_right _ ⟨s, rfl⟩
    have hst : e₃ s = e₂ t := by
      apply Complex.ext
      · exact hs.trans ht.symm
      · exact (hconst _ hsγ).trans (hconst _ htγ).symm
    have hinter' : e₂ t ∈ Set.range e₂ ∩ Set.range e₃ := by
      exact ⟨⟨t, rfl⟩, ⟨s, hst⟩⟩
    rw [hinter] at hinter'
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hinter') with h | h
    · change (e₂ t).re = r at ht
      rw [h] at ht
      dsimp [r] at ht
      linarith
    · change (e₂ t).re = r at ht
      rw [h] at ht
      dsimp [r] at ht
      linarith
  · obtain ⟨u, v, hu, hv, huv, e₂, e₃, he₂, he₃, h0₂, h1₂, h0₃, h1₃, hun, hinter⟩ :=
      Topology.circle_split_two_arcs γ hγ a b ha hb hab
    have hc₂ : Continuous (fun t : unitInterval ↦ (e₂ t).re) :=
      Complex.continuous_re.comp (he₂.continuous)
    have hc₃ : Continuous (fun t : unitInterval ↦ (e₃ t).re) :=
      Complex.continuous_re.comp (he₃.continuous)
    let r : ℝ := (a.re + b.re) / 2
    have hra : b.re ≤ r := by dsimp [r]; linarith
    have hrb : r ≤ a.re := by dsimp [r]; linarith
    obtain ⟨t, ht⟩ := (intermediate_value_univ (1 : unitInterval) (0 : unitInterval) hc₂)
      ⟨by simpa [h1₂] using hra, by simpa [h0₂] using hrb⟩
    obtain ⟨s, hs⟩ := (intermediate_value_univ (0 : unitInterval) (1 : unitInterval) hc₃)
      ⟨by simpa [h0₃] using hra, by simpa [h1₃] using hrb⟩
    have htγ : e₂ t ∈ Set.range γ := by
      rw [← hun]
      exact mem_union_left _ ⟨t, rfl⟩
    have hsγ : e₃ s ∈ Set.range γ := by
      rw [← hun]
      exact mem_union_right _ ⟨s, rfl⟩
    have hst : e₃ s = e₂ t := by
      apply Complex.ext
      · exact hs.trans ht.symm
      · exact (hconst _ hsγ).trans (hconst _ htγ).symm
    have hinter' : e₂ t ∈ Set.range e₂ ∩ Set.range e₃ := by
      exact ⟨⟨t, rfl⟩, ⟨s, hst⟩⟩
    rw [hinter] at hinter'
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hinter') with h | h
    · change (e₂ t).re = r at ht
      rw [h] at ht
      dsimp [r] at ht
      linarith
    · change (e₂ t).re = r at ht
      rw [h] at ht
      dsimp [r] at ht
      linarith

/-- The upper and lower ordinate contacts of an embedded circle are distinct. -/
theorem cairns_extreme_contact_distinct_extrema
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ)
    (P₁ P₂ : ℂ) (_hP₁ : P₁ ∈ Set.range γ) (hP₂ : P₂ ∈ Set.range γ)
    (hmax : ∀ z ∈ Set.range γ, z.im ≤ P₁.im)
    (hmin : ∀ z ∈ Set.range γ, P₂.im ≤ z.im) : P₁ ≠ P₂ := by
  intro heq
  subst P₂
  apply cairns_embedded_circle_ordinate_nonconstant γ hγ P₁.im
  intro z hz
  exact le_antisymm (hmax z hz) (hmin z hz)

/--
An embedded circle cannot have equal upper and lower ordinate extrema.  If the
extreme ordinates agreed, the two embedded arcs obtained by cutting at the
extreme points would each attain an intermediate real coordinate; their arc
intersection would then contain a third point.

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
§5, together with the two-arc decomposition from Whyburn, Chapter II §5.
-/
theorem cairns_extreme_contact_strict_extrema
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ)
    (P₁ P₂ : ℂ) (hP₁ : P₁ ∈ Set.range γ) (hP₂ : P₂ ∈ Set.range γ)
    (hmax : ∀ z ∈ Set.range γ, z.im ≤ P₁.im)
    (hmin : ∀ z ∈ Set.range γ, P₂.im ≤ z.im)
    (hne : P₁ ≠ P₂) : P₂.im < P₁.im := by
  by_contra hnot
  have heq : P₂.im = P₁.im := le_antisymm (hmin P₁ hP₁) (le_of_not_gt hnot)
  have hres : P₂.re ≠ P₁.re := by
    intro hre
    apply hne
    exact Complex.ext hre.symm heq.symm
  obtain hlt | hgt := lt_or_gt_of_ne hres
  · obtain ⟨u, v, hu, hv, huv, e₂, e₃, he₂, he₃, h0₂, h1₂, h0₃, h1₃, hun, hinter⟩ :=
      Topology.circle_split_two_arcs γ hγ P₂ P₁ hP₂ hP₁ hne.symm
    have hc₂ : Continuous (fun t : unitInterval ↦ (e₂ t).re) :=
      Complex.continuous_re.comp (he₂.continuous)
    have hc₃ : Continuous (fun t : unitInterval ↦ (e₃ t).re) :=
      Complex.continuous_re.comp (he₃.continuous)
    let r : ℝ := (P₂.re + P₁.re) / 2
    have hr₂ : P₂.re ≤ r := by dsimp [r]; linarith
    have hr₁ : r ≤ P₁.re := by dsimp [r]; linarith
    obtain ⟨t, ht⟩ := (intermediate_value_univ (0 : unitInterval) (1 : unitInterval) hc₂)
      ⟨by simpa [h0₂] using hr₂, by simpa [h1₂] using hr₁⟩
    obtain ⟨s, hs⟩ := (intermediate_value_univ (1 : unitInterval) (0 : unitInterval) hc₃)
      ⟨by simpa [h1₃] using hr₂, by simpa [h0₃] using hr₁⟩
    have htval : (e₂ t).re = r := ht
    have hsval : (e₃ s).re = r := hs
    have htγ : e₂ t ∈ Set.range γ := by
      rw [← hun]
      exact mem_union_left _ ⟨t, rfl⟩
    have hsγ : e₃ s ∈ Set.range γ := by
      rw [← hun]
      exact mem_union_right _ ⟨s, rfl⟩
    have htim : (e₂ t).im = P₂.im := by
      apply le_antisymm
      · rw [heq]
        exact hmax _ htγ
      · exact hmin _ htγ
    have hsim : (e₃ s).im = P₂.im := by
      apply le_antisymm
      · rw [heq]
        exact hmax _ hsγ
      · exact hmin _ hsγ
    have hst : e₃ s = e₂ t := by
      apply Complex.ext
      · exact hsval.trans htval.symm
      · exact hsim.trans htim.symm
    have hinter' : e₂ t ∈ Set.range e₂ ∩ Set.range e₃ := by
      exact ⟨⟨t, rfl⟩, ⟨s, hst⟩⟩
    rw [hinter] at hinter'
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hinter') with h | h
    · rw [h] at htval
      dsimp [r] at htval
      linarith
    · rw [h] at htval
      dsimp [r] at htval
      linarith
  · obtain ⟨u, v, hu, hv, huv, e₂, e₃, he₂, he₃, h0₂, h1₂, h0₃, h1₃, hun, hinter⟩ :=
      Topology.circle_split_two_arcs γ hγ P₂ P₁ hP₂ hP₁ hne.symm
    have hc₂ : Continuous (fun t : unitInterval ↦ (e₂ t).re) :=
      Complex.continuous_re.comp (he₂.continuous)
    have hc₃ : Continuous (fun t : unitInterval ↦ (e₃ t).re) :=
      Complex.continuous_re.comp (he₃.continuous)
    let r : ℝ := (P₂.re + P₁.re) / 2
    have hr₂ : P₁.re ≤ r := by dsimp [r]; linarith
    have hr₁ : r ≤ P₂.re := by dsimp [r]; linarith
    obtain ⟨t, ht⟩ := (intermediate_value_univ (1 : unitInterval) (0 : unitInterval) hc₂)
      ⟨by simpa [h1₂] using hr₂, by simpa [h0₂] using hr₁⟩
    obtain ⟨s, hs⟩ := (intermediate_value_univ (0 : unitInterval) (1 : unitInterval) hc₃)
      ⟨by simpa [h0₃] using hr₂, by simpa [h1₃] using hr₁⟩
    have htval : (e₂ t).re = r := ht
    have hsval : (e₃ s).re = r := hs
    have htγ : e₂ t ∈ Set.range γ := by
      rw [← hun]
      exact mem_union_left _ ⟨t, rfl⟩
    have hsγ : e₃ s ∈ Set.range γ := by
      rw [← hun]
      exact mem_union_right _ ⟨s, rfl⟩
    have htim : (e₂ t).im = P₂.im := by
      apply le_antisymm
      · rw [heq]
        exact hmax _ htγ
      · exact hmin _ htγ
    have hsim : (e₃ s).im = P₂.im := by
      apply le_antisymm
      · rw [heq]
        exact hmax _ hsγ
      · exact hmin _ hsγ
    have hst : e₃ s = e₂ t := by
      apply Complex.ext
      · exact hsval.trans htval.symm
      · exact hsim.trans htim.symm
    have hinter' : e₂ t ∈ Set.range e₂ ∩ Set.range e₃ := by
      exact ⟨⟨t, rfl⟩, ⟨s, hst⟩⟩
    rw [hinter] at hinter'
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hinter') with h | h
    · rw [h] at htval
      dsimp [r] at htval
      linarith
    · rw [h] at htval
      dsimp [r] at htval
      linarith

end HolomorphicAnosov
