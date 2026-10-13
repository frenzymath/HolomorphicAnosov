import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BoundedInvariantBlockFamily
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.InvariantBlockSignedSum
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Fin

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped BigOperators Classical
noncomputable section

/-- The signed sum over length-tagged invariant block families is one when
the positive length bound contains the alphabet. Sum over the length tag; the
zero-length fibre is empty, and every positive tag gives the invariant-family
cardinality in the public cancellation theorem. Source: Manning (1971), pp.218–219. -/
theorem bounded_invariant_family_signed_sum {A : Type*} [Fintype A] [DecidableEq A]
    [Nonempty A] (g : A ≃ A) (q : ℕ) (hq : Fintype.card A ≤ q) :
    ∑ U : BoundedInvariantBlockFamily g q, (-1 : ℤ) ^ (U.1.val + 1) = 1 := by
  classical
  rw [Fintype.sum_sigma, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h := invariant_block_signed_sum g q hq
  rw [← Fin.sum_univ_eq_sum_range] at h
  convert h using 1
  simp only [Nat.succ_pos, true_and, Nat.card_eq_fintype_card, mul_comm, Nat.add_assoc]
  simp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro U _
  exact Nat.not_lt_zero _ U.property.1

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
