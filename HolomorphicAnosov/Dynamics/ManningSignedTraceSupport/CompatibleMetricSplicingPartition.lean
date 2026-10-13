import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompatibleMetricModulus
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SplicingOriginalRectangle
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SplicingOriginalMarkov

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set BowenBasicSetCoding

/-- A compact identity modulus converts sufficiently small splice errors in a
compatible metric into rectangle and Markov laws for a fixed original-metric
plaque radius. Choose the modulus at the plaque radius. The splice rectangle
lemma uses twice that radius below the expansive bound, and the splice Markov
lemma uses the same sum bound. The rectangles and coding are never changed.
This is an agent-expanded metric handoff in Manning's partition construction. -/
theorem compatible_metric_splicing_partition {X : Type*} [old : MetricSpace X]
    [CompactSpace X] (new : MetricSpace X)
    (ht : new.toUniformSpace.toTopologicalSpace = old.toUniformSpace.toTopologicalSpace)
    (F : @Homeomorph X X old.toUniformSpace.toTopologicalSpace
      old.toUniformSpace.toTopologicalSpace) {e b : ℝ} (hb : 0 < b) (hbe : 2 * b ≤ e)
    (hexp : ∀ x y : X,
      (∀ j : ℤ, old.dist ((F ^ j) x) ((F ^ j) y) ≤ e) → x = y) :
    letI : MetricSpace X := old
    ∃ δ > 0, ∀ (N : ℕ) (R : Fin N → Set X) (B : Fin N → Fin N → Prop)
      (coding : CodeSpace B → X),
      (∀ i, (R i).Nonempty ∧ IsCompact (R i) ∧ R i = closure (interior (R i))) →
      (∀ i j, i ≠ j → Disjoint (interior (R i)) (interior (R j))) →
      (∀ a : CodeSpace B, ∀ j : ℤ, (F ^ j) (coding a) ∈ R (a.val j)) →
      (∀ x i, x ∈ R i → ∃ a : CodeSpace B, coding a = x ∧ a.val 0 = i) →
      (∀ a d : CodeSpace B, a.val 0 = d.val 0 → ∃ c : CodeSpace B,
        (∀ j : ℤ, j ≤ 0 → c.val j = a.val j) ∧
        (∀ j : ℤ, 0 ≤ j → c.val j = d.val j) ∧
        (∀ j : ℤ, 0 ≤ j → new.dist ((F ^ j) (coding c)) ((F ^ j) (coding d)) < δ) ∧
        (∀ j : ℤ, j ≤ 0 → new.dist ((F ^ j) (coding c)) ((F ^ j) (coding a)) < δ)) →
      (∀ i, IsRectangle F old.dist b (R i)) ∧ HasMarkovInclusions F old.dist b R := by
  let : MetricSpace X := old
  obtain ⟨δ, hδ, hmod⟩ := @compatible_metric_modulus X old (inferInstance : @CompactSpace X old.toUniformSpace.toTopologicalSpace) new ht b hb
  refine ⟨δ, hδ, ?_⟩
  intro N R B coding hshape hdisjoint horbit hlabel hsplice
  have hspliceOld : ∀ a d : CodeSpace B, a.val 0 = d.val 0 → ∃ c : CodeSpace B,
      (∀ j : ℤ, j ≤ 0 → c.val j = a.val j) ∧
      (∀ j : ℤ, 0 ≤ j → c.val j = d.val j) ∧
      (∀ j : ℤ, 0 ≤ j → old.dist ((F ^ j) (coding c)) ((F ^ j) (coding d)) < b) ∧
      (∀ j : ℤ, j ≤ 0 → old.dist ((F ^ j) (coding c)) ((F ^ j) (coding a)) < b) := by
    intro a d had
    obtain ⟨c, hp, hf, hs, hu⟩ := hsplice a d had
    exact ⟨c, hp, hf, fun j hj ↦ hmod _ _ (hs j hj),
      fun j hj ↦ hmod _ _ (hu j hj)⟩
  refine ⟨splicing_original_rectangle F R B coding le_rfl hbe hexp hshape
    horbit hlabel hspliceOld, ?_⟩
  exact splicing_original_markov F R B coding (ε := b) hb.le (by linarith) hexp
    (fun i ↦ (hshape i).2.2) hdisjoint horbit hlabel hspliceOld


end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
