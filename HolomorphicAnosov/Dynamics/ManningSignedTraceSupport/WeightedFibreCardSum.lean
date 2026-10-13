import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.SetTheory.Cardinal.Finite

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped BigOperators Classical
noncomputable section

/-- Summing weighted fibre cardinalities over a finite physical space recovers
the weighted total cardinality of each symbolic family. Apply finite fibrewise
summation to each family and interchange the two finite sums. This is the final
finite counting interchange in Manning (1971), pp.218–219. -/
theorem weighted_fibre_card_sum {C X : Type*} [Fintype C] [Fintype X]
    (W : C → Type*) [∀ c, Fintype (W c)] (p : ∀ c, W c → X) (s : C → ℤ) :
    ∑ x : X, ∑ c : C, s c * Nat.card {w : W c // p c w = x} =
      ∑ c : C, s c * Nat.card (W c) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.mul_sum]
  congr 1
  have h := Fintype.sum_fiberwise (p c) (fun _ : W c ↦ (1 : ℤ))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Nat.card_eq_fintype_card] using h

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
