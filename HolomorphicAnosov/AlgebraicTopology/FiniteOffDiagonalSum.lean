import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite double sums with their diagonal removed

The row and column enumerations of the off-diagonal entries give the same sum.
This supplies the finite-index transposition in Hatcher's signed prism proof,
Algebraic Topology, Theorem 3.11, p.212. The proof of this generic algebraic
lemma is an explicit agent-written indexing argument using Mathlib finite sums.
DAG node: `algebra.fin_off_diagonal_sum_g14`.
-/

open scoped BigOperators

namespace HolomorphicAnosov

/-- A finite matrix can be summed off its diagonal either rowwise or columnwise.

Source: explicit finite-index expansion of Hatcher, *Algebraic Topology*, Theorem 3.11,
p. 212. Proof: split each row into its diagonal entry and its `succAbove`-indexed
complement, and do the same for each column. The full sums agree by sum commutation;
cancelling their equal diagonal sums gives the result, also when `n = 0`. -/
theorem fin_sum_offDiagonal_transpose {A : Type*} [AddCommGroup A] (n : ℕ)
    (f : Fin (n+1) → Fin (n+1) → A) :
    (∑ i : Fin (n+1), ∑ k : Fin n, f i (i.succAbove k)) =
      ∑ j : Fin (n+1), ∑ k : Fin n, f (j.succAbove k) j := by
  have hr : (∑ i, ∑ j, f i j) = (∑ i, f i i) +
      ∑ i, ∑ k : Fin n, f i (i.succAbove k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact Fin.sum_univ_succAbove (fun j ↦ f i j) i
  have hc : (∑ j, ∑ i, f i j) = (∑ j, f j j) +
      ∑ j, ∑ k : Fin n, f (j.succAbove k) j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact Fin.sum_univ_succAbove (fun i ↦ f i j) j
  apply add_left_cancel (a := ∑ i, f i i)
  rw [← hr, ← hc, Finset.sum_comm]

/-- If every off-diagonal matrix entry cancels its column-indexed partner,
then the sum of the matrix and all partners is its diagonal sum.

Source: explicit finite-index expansion of Hatcher, *Algebraic Topology*, Theorem 3.11,
p. 212. Proof: split the matrix sum at its diagonal, transpose the off-diagonal sum,
then distribute sums to cancel each entry with its partner using `h`. -/
theorem fin_double_sum_cancel_offDiagonal {A : Type*} [AddCommGroup A] (n : ℕ)
    (f : Fin (n+1) → Fin (n+1) → A) (b : Fin (n+1) → Fin n → A)
    (h : ∀ j k, f (j.succAbove k) j + b j k = 0) :
    (∑ i, ∑ j, f i j) + (∑ j, ∑ k, b j k) = ∑ i, f i i := by
  have hr : (∑ i, ∑ j, f i j) = (∑ i, f i i) +
      ∑ i, ∑ k : Fin n, f i (i.succAbove k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact Fin.sum_univ_succAbove (fun j ↦ f i j) i
  rw [hr, fin_sum_offDiagonal_transpose, add_assoc, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  simp [h]

/-- Cancellation of a square face array against a boundary-prism array,
with its diagonal split into the two distinguished faces. This is the finite-sum
assembly used after a prism boundary has been partitioned into lateral and
diagonal faces.

Source: explicit finite-index expansion of Hatcher, *Algebraic Topology*, Theorem 3.11,
p. 212. Proof: apply off-diagonal cancellation, replace each surviving diagonal
entry using `hdiag`, and distribute the sum over the two summands. -/
theorem fin_double_sum_cancel_diagonal_pair {A : Type*} [AddCommGroup A] (n : ℕ)
    (f : Fin (n+1) → Fin (n+1) → A) (b : Fin (n+1) → Fin n → A)
    (lower upper : Fin (n+1) → A)
    (hdiag : ∀ i, f i i = lower i + upper i)
    (hoff : ∀ j k, f (j.succAbove k) j + b j k = 0) :
    (∑ i, ∑ j, f i j) + (∑ j, ∑ k, b j k) =
      (∑ i, lower i) + (∑ i, upper i) := by
  rw [fin_double_sum_cancel_offDiagonal n f b hoff, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ hdiag i

end HolomorphicAnosov
