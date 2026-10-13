import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.MatchedLabelsCode
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.RelatedCodesSameImage

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
open Set BowenBasicSetCoding
open scoped Classical
noncomputable section

/-- A two-sided matched block itinerary has a common physical image. Follow one
label to obtain a reference code. Every other block label extends to a code by
the public matching-path theorem. At every time the two labels have the supplied
common rectangle point, so small-mesh expansivity identifies their coding images.
The reference image therefore belongs to every requested rectangle at every time.
This is the common-image-first step of de Jong, §3.2 pp.2464–2465, with Manning's
related-code lemma; no periodic-fibre or unique-matching assertion is used. -/
theorem matched_blocks_common_image {X : Type*} [MetricSpace X] [CompactSpace X]
    (F : X ≃ₜ X) {N : ℕ} (R : Fin N → Set X) (B : Fin N → Fin N → Prop)
    (coding : CodeSpace B → X) (T : Matrix (Fin N) (Fin N) ℤ)
    (hT : ∀ i k, T i k = 1 ↔ B i k) {e : ℝ}
    (hexp : ∀ x y : X, (∀ j : ℤ, dist ((F ^ j) x) ((F ^ j) y) ≤ e) → x = y)
    (hsmall : ∀ i, Metric.diam (R i) < e / 2)
    (horbit : ∀ a : CodeSpace B, ∀ j : ℤ, (F ^ j) (coding a) ∈ R (a.val j))
    {K : Type*} [Nonempty K] (S : ℤ → K → Finset (Fin N))
    (hne : ∀ j k, (S j k).Nonempty)
    (hcommon : ∀ j, ∃ x : X, ∀ k i, i ∈ S j k → x ∈ R i)
    (hmatch : ∀ j k, BlockMatching T (S j k) (S (j + 1) k)) :
    ∃ x : X, ∀ j k i, i ∈ S j k → (F ^ j) x ∈ R i := by
  let k₀ : K := Classical.choice inferInstance
  obtain ⟨i₀, hi₀⟩ := hne 0 k₀
  obtain ⟨a, ha₀, ha⟩ := matched_labels_code B T hT (fun j ↦ S j k₀)
    (fun j ↦ hmatch j k₀) 0 i₀ hi₀
  refine ⟨coding a, ?_⟩
  intro j k i hi
  obtain ⟨b, hbi, hb⟩ := matched_labels_code B T hT (fun j ↦ S j k)
    (fun j ↦ hmatch j k) j i hi
  have hab : coding a = coding b := by
    apply related_codes_same_image F R B coding hexp hsmall horbit
    intro l
    obtain ⟨z, hz⟩ := hcommon l
    exact ⟨z, hz k₀ _ (ha l), hz k _ (hb l)⟩
  simpa only [hab, hbi] using horbit b j

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
