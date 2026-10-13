import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWordEqOfZero
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SupportedAlphabetCardBound

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open Set
open scoped Classical
noncomputable section

/-- Tuple words supported on one physical point inject into their initial supported symbols, giving the uniform fibre bound `(q+1)^q`. (Manning, pp. 218–219) -/
theorem periodicWord_fibre_card_bound {X : Type*} (F : X → X) {N r m : ℕ}
    (R : Fin N → Set X) (T : Matrix (Fin N) (Fin N) ℤ) (c : Composition r)
    (hm : 0 < m) (hr : r ≤ overlapMultiplicity R) (x : X)
    (hunique : ∀ n : ℕ, ∀ i j k : Fin N,
      (F^[n]) x ∈ R i → (F^[n + 1]) x ∈ R j → (F^[n + 1]) x ∈ R k →
      T i j = 1 → T i k = 1 → j = k) :
    Nat.card {w : PeriodicWord R T c hm // x ∈ periodicPhysicalPoints R T c F hm w} ≤
      (overlapMultiplicity R + 1) ^ overlapMultiplicity R := by
  classical
  let ev : {w : PeriodicWord R T c hm // x ∈ periodicPhysicalPoints R T c F hm w} →
      {s : Alphabet R c // ∀ k i, i ∈ s.val k → x ∈ R i} :=
    fun w ↦ ⟨w.val.val ⟨0, hm⟩, fun k i hi ↦ by simpa using w.property.2 ⟨0, hm⟩ k i hi⟩
  have hinj : Function.Injective ev := by
    intro w v h
    apply Subtype.ext
    exact periodicWord_eq_of_zero F R T c hm hunique w.property v.property
      (congrArg Subtype.val h)
  have hfirst := (Nat.card_le_card_of_injective ev hinj).trans
    (supportedAlphabet_card_bound R c x)
  have hlen : c.length + 1 ≤ overlapMultiplicity R + 1 := by
    exact Nat.add_le_add_right (c.length_le.trans hr) 1
  exact hfirst.trans ((Nat.pow_le_pow_left hlen _).trans
    (Nat.pow_le_pow_right (by omega) (label_card_le_overlapMultiplicity R x)))

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
