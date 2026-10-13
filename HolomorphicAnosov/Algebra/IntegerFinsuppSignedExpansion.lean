import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Signed unit expansion of a finitely supported integer function

Source: Hatcher, *Algebraic Topology*, proof of Theorem 2A.1, p.167,
where relabeling a finite chain permits all coefficients to be ±1.
The explicit finite-copy argument below is the agent-written expansion of
that step recorded in `algebra.integer_finsupp_signed_expansion_g12`.
-/

open scoped BigOperators

namespace HolomorphicAnosov

/-- Every finitely supported integer function is a finite sum of signed unit generators.

Source: Hatcher, *Algebraic Topology*, proof of Theorem 2A.1, p.167.

Proof: For each label in the finite support, take as many copies as the absolute value
of its integer coefficient. Assign every copy sign -1 when that coefficient is negative
and sign +1 otherwise. Summing the signed unit functions in this fibre gives the single
function with the original coefficient, by integer absolute-value arithmetic. Sum over
the finite dependent union of the fibres, using `Fintype.sum_sigma`, and then use
`Finsupp.sum_single` to recover the original function. Enumerate this finite dependent
union by `Fin m` with `Fintype.equivFinOfCardEq` and reindex with `Equiv.sum_comp`.
For zero support the union and `Fin m` are empty, so the sum is zero. Repeated labels
are permitted, and no finiteness or nonemptiness assumption on the label type is needed.
-/
theorem integerFinsuppSignedExpansion {A : Type*} (c : A →₀ ℤ) :
    ∃ (m : ℕ) (a : Fin m → A) (ε : Fin m → ℤ),
      (∀ i, ε i = -1 ∨ ε i = 1) ∧
      c = ∑ i, ε i • Finsupp.single (a i) (1 : ℤ) := by
  classical
  let I := Σ a : c.support, Fin (c a.val).natAbs
  let sign : c.support → ℤ := fun a ↦ if c a.val < 0 then -1 else 1
  have hsum : (∑ i : I, sign i.1 • Finsupp.single i.1.val (1 : ℤ)) = c := by
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hfibre (a : c.support) :
        (c a.val).natAbs • (sign a • Finsupp.single a.val (1 : ℤ)) =
          Finsupp.single a.val (c a.val) := by
      rw [Finsupp.smul_single, Finsupp.smul_single]
      congr 1
      simp only [smul_eq_mul, mul_one, nsmul_eq_mul]
      dsimp [sign]
      split_ifs with h
      · rw [Int.natCast_natAbs, abs_of_neg h]
        ring
      · rw [Int.natCast_natAbs, abs_of_nonneg (le_of_not_gt h)]
        ring
    simp_rw [hfibre]
    calc
      (∑ a : c.support, Finsupp.single a.val (c a.val)) =
          ∑ a ∈ c.support, Finsupp.single a (c a) :=
        Finset.sum_attach c.support (fun a ↦ Finsupp.single a (c a))
      _ = c := c.sum_single
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFinOfCardEq (rfl : Fintype.card I = Fintype.card I)).symm
  refine ⟨Fintype.card I, fun i ↦ (e i).1.val, fun i ↦ sign (e i).1, ?_, ?_⟩
  · intro i
    dsimp [sign]
    split_ifs <;> simp
  · exact hsum.symm.trans (Equiv.sum_comp e (fun i : I ↦ sign i.1 • Finsupp.single i.1.val (1 : ℤ))).symm

end HolomorphicAnosov
