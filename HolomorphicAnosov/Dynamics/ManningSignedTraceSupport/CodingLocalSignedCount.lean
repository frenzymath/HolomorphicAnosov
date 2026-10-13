import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SignedTraceSum
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SupportedWordSignedSum
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.FibreCoordinateEquiv
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.NoCrossTransition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicZpowRemainder
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicPhysicalPoints
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphZpowEquiv
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphPowCoe

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
open Set BowenBasicSetCoding
open scoped BigOperators Classical
noncomputable section

/-- The actual coding fibre of a periodic physical point contributes one to
Manning's signed periodic-word count. Coordinate rigidity makes the finite
fibre inject into labels; evaluation at zero and at the return time identify
its return permutation. Period reduction supplies the finite orbit, and the
public no-cross theorem supplies the forced edges. Apply the supported-word
signed sum. Source: Manning (1971), pp.217–219. -/
theorem coding_local_signed_count {X : Type*} [MetricSpace X] [CompactSpace X]
    (F : X ≃ₜ X) {N : ℕ} (R : Fin N → Set X) (B : Fin N → Fin N → Prop)
    (coding : CodeSpace B → X) (T : Matrix (Fin N) (Fin N) ℤ)
    (hT : ∀ i k, T i k = 1 ↔ B i k) {e : ℝ}
    (hexp : ∀ x y : X, (∀ j : ℤ, dist ((F ^ j) x) ((F ^ j) y) ≤ e) → x = y)
    (hsmall : ∀ i, Metric.diam (R i) < e / 2)
    (horbit : ∀ a : CodeSpace B, ∀ j : ℤ, (F ^ j) (coding a) ∈ R (a.val j))
    {m q : ℕ} (hm : 0 < m) (x : X) (hper : ((F : X → X)^[m]) x = x)
    (hne : ∃ a : CodeSpace B, coding a = x)
    (hrigid : ∀ a b : CodeSpace B, coding a = x → coding b = x →
      (∃ j : ℤ, a.val j = b.val j) → a = b)
    (hlabel : ∀ j i, (F ^ j) x ∈ R i →
      ∃ a : CodeSpace B, coding a = x ∧ a.val j = i)
    (hq : Nat.card {a : CodeSpace B // coding a = x} ≤ q) :
    ∑ c : PositiveComposition q, (-1 : ℤ) ^ (c.2.length + 1) *
      Nat.card {w : PeriodicWord R T c.2 hm //
        x ∈ periodicPhysicalPoints R T c.2 F hm w} = 1 := by
  classical
  let A := {a : CodeSpace B // coding a = x}
  let l : ℤ → A → Fin N := fun j a ↦ a.val.val j
  have hl (j : ℤ) : Function.Injective (l j) := by
    intro a b h
    exact Subtype.ext (hrigid a.val b.val a.property b.property ⟨j, h⟩)
  let : Finite A := Finite.of_injective (l 0) (hl 0)
  let : Fintype A := Fintype.ofFinite A
  let : Nonempty A := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hpow : (F ^ (m : ℤ)) x = x := by
    simpa only [zpow_natCast, CarrierAdapter.homeomorph_pow_coe] using hper
  let L : Set (Fin N) := {i | x ∈ R i}
  let E0 : A ≃ L := fibreCoordinateEquiv B coding x 0 L
    (fun a ha ↦ by simpa only [L, Set.mem_ofPred_eq, ha, zpow_zero, Homeomorph.one_apply] using horbit a 0)
    (fun a b ha hb hij ↦ hrigid a b ha hb ⟨0, hij⟩)
    (fun i hi ↦ hlabel 0 i (by simpa only [L, Set.mem_ofPred_eq, zpow_zero, Homeomorph.one_apply] using hi))
  let Em : A ≃ L := fibreCoordinateEquiv B coding x m L
    (fun a ha ↦ by simpa only [L, Set.mem_ofPred_eq, ha, hpow] using horbit a m)
    (fun a b ha hb hij ↦ hrigid a b ha hb ⟨m, hij⟩)
    (fun i hi ↦ hlabel m i (by simpa only [L, Set.mem_ofPred_eq, hpow] using hi))
  let g : A ≃ A := Em.trans E0.symm
  have hreturn (a : A) : l (m : ℤ) a = l 0 (g a) := by
    have h := congrArg Subtype.val (E0.apply_symm_apply (Em a))
    exact h.symm
  have hrem (j : ℤ) : (F ^ j) x =
      ((F : X → X)^[(integerPeriodicTime hm j).val]) x := by
    simpa only [← CarrierAdapter.homeomorph_zpow_equiv, Homeomorph.coe_toEquiv, integerPeriodicTime]
      using periodic_zpow_remainder F.toEquiv hm hper j
  have h := supported_word_signed_sum (A := A) R T hm l hl
    (by
      intro j a b hab
      apply Subtype.ext
      by_contra hab'
      exact no_cross_transition F R B coding hexp hsmall horbit hrigid
        a.property b.property hab' j ((hT _ _).mp hab))
    (fun j a ↦ (hT _ _).mpr (a.val.property j))
    (fun t ↦ ((F : X → X)^[t.val]) x)
    (fun j a ↦ by simpa only [← hrem j, a.property] using horbit a.val j)
    (by
      intro j i hi
      obtain ⟨a, ha, hai⟩ := hlabel j i (by simpa only [hrem j] using hi)
      exact ⟨⟨a, ha⟩, hai⟩)
    g hreturn (by simpa only [Nat.card_eq_fintype_card] using hq)
  simpa only [periodicPhysicalPoints, Set.mem_ofPred_eq, hper, true_and] using h

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
