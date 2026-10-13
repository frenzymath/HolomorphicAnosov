import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PositiveComposition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWord
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWordInvariantBlocksEquiv
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompositionInvariantSignedSum

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open Set CodingAdapter
open scoped BigOperators Classical
noncomputable section

/-- The local signed count of all periodic tuple words supported on one physical
orbit is one when coordinate maps identify its nonempty finite fibre, legal
edges follow fibre elements, and the fibre return is a permutation. For each
composition apply the public word/block equivalence and then the composition
indexed invariant-family cancellation. Source: Manning (1971), pp.218–219. -/
theorem supported_word_signed_sum {A X : Type*} [Fintype A] [Nonempty A]
    {N m q : ℕ} (R : Fin N → Set X) (T : Matrix (Fin N) (Fin N) ℤ)
    (hm : 0 < m) (l : ℤ → A → Fin N) (hl : ∀ j, Function.Injective (l j))
    (hforced : ∀ j a b, T (l j a) (l (j + 1) b) = 1 → a = b)
    (hedge : ∀ j a, T (l j a) (l (j + 1) a) = 1)
    (x : Fin m → X) (hx : ∀ j a, x (integerPeriodicTime hm j) ∈ R (l j a))
    (hlabel : ∀ j i, x (integerPeriodicTime hm j) ∈ R i → ∃ a, l j a = i)
    (g : A ≃ A) (hreturn : ∀ a, l (m : ℤ) a = l 0 (g a))
    (hq : Fintype.card A ≤ q) :
    ∑ c : PositiveComposition q, (-1 : ℤ) ^ (c.2.length + 1) *
      Nat.card {w : PeriodicWord R T c.2 hm //
        ∀ t k i, i ∈ (w.val t).val k → x t ∈ R i} = 1 := by
  classical
  convert composition_invariant_signed_sum g q hq using 1
  apply Finset.sum_congr rfl
  intro c _
  rw [Nat.card_congr (periodicWordInvariantBlocksEquiv R T c.2 hm l hl hforced hedge
    x hx hlabel g hreturn)]

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
