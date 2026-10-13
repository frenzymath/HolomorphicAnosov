import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PositiveComposition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.WeightedFibreCardSum
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWordCardEqTrace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SignedTraceSum

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open Set
open scoped BigOperators Classical
noncomputable section

/-- If each physical fibre contributes signed count one, the total number of periodic words equals the signed trace sum. (Manning, pp. 218–219) -/
theorem signedTrace_of_local_count {X Y : Type*} [Fintype Y] {N q m : ℕ}
    (R : Fin N → Set X) (T : Matrix (Fin N) (Fin N) ℤ) (hm : 0 < m)
    (p : ∀ c : PositiveComposition q, PeriodicWord R T c.2 hm → Y)
    (hlocal : ∀ y : Y, ∑ c : PositiveComposition q,
      (-1 : ℤ) ^ (c.2.length + 1) *
        Nat.card {w : PeriodicWord R T c.2 hm // p c w = y} = 1) :
    (Nat.card Y : ℤ) = signedTraceSum R T q m := by
  classical
  have h := weighted_fibre_card_sum (fun c : PositiveComposition q ↦
    PeriodicWord R T c.2 hm) p (fun c ↦ (-1 : ℤ) ^ (c.2.length + 1))
  simp only [hlocal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Nat.card_eq_fintype_card] at h
  rw [h]
  unfold signedTraceSum
  apply Finset.sum_congr rfl
  intro c _
  rw [periodicWord_card_eq_trace R T c.2 hm]

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
