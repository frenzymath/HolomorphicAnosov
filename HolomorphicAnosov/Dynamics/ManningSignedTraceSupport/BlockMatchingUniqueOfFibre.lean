import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.FibreEdgeTargetUnique
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockMatching

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter

open Set
open BowenBasicSetCoding
noncomputable section

/-- Two blocks supported on consecutive points of one rigid coding fibre have
at most one legal matching. For each source label choose its fibre code; the
public forced-successor lemma identifies the target of every legal matching
with that code's next label. Pointwise equality gives equality of equivalences.
An existing block matching therefore has the required unique-existence form.
Source argument: Manning (1971), Lemma 2 p.217 and block matrices pp.218–219. -/
theorem blockMatching_unique_of_fibre {X : Type*} [MetricSpace X] [CompactSpace X]
    (F : X ≃ₜ X) {N : ℕ} (R : Fin N → Set X) (B : Fin N → Fin N → Prop)
    (coding : CodeSpace B → X) (T : Matrix (Fin N) (Fin N) ℤ)
    (hT : ∀ i k, T i k = 1 ↔ B i k) {e : ℝ}
    (hexp : ∀ x y : X, (∀ j : ℤ, dist ((F ^ j) x) ((F ^ j) y) ≤ e) → x = y)
    (hsmall : ∀ i, Metric.diam (R i) < e / 2)
    (horbit : ∀ a : CodeSpace B, ∀ j : ℤ, (F ^ j) (coding a) ∈ R (a.val j))
    {x : X}
    (hrigid : ∀ a b : CodeSpace B, coding a = x → coding b = x →
      (∃ j : ℤ, a.val j = b.val j) → a = b)
    (hlabel : ∀ j i, (F ^ j) x ∈ R i →
      ∃ a : CodeSpace B, coding a = x ∧ a.val j = i)
    (j : ℤ) {s t : Finset (Fin N)}
    (hs : ∀ i ∈ s, (F ^ j) x ∈ R i)
    (ht : ∀ i ∈ t, (F ^ (j + 1)) x ∈ R i)
    (hmatch : BlockMatching T s t) :
    ∃! a : ↥s ≃ ↥t, ∀ i, T i.val (a i).val = 1 := by
  obtain ⟨a, ha⟩ := hmatch
  refine ⟨a, ha, ?_⟩
  intro d hd
  apply Equiv.ext
  intro i
  apply Subtype.ext
  obtain ⟨c, hc, hci⟩ := hlabel j i.val (hs i.val i.property)
  have hda := fibre_edge_target_unique F R B coding hexp hsmall horbit hrigid hlabel
    hc j (ht (d i).val (d i).property)
    (hci.symm ▸ (hT i.val (d i).val).mp (hd i))
  have haa := fibre_edge_target_unique F R B coding hexp hsmall horbit hrigid hlabel
    hc j (ht (a i).val (a i).property)
    (hci.symm ▸ (hT i.val (a i).val).mp (ha i))
  exact hda.trans haa.symm


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
