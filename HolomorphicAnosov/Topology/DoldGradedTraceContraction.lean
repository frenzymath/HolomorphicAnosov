import Mathlib.LinearAlgebra.Trace

noncomputable section
open TensorProduct
open scoped BigOperators
namespace HolomorphicAnosov
universe u

/-- The degreewise Dold sign converts tensor evaluation into the alternating trace.

Source: Dold (1965), (3.2)–(3.4), pp.4–5. In degree `k`, the signed tensor-to-map
identification multiplies the usual dual tensor homomorphism by `(-1)^(k*k)`.
Mathlib identifies its unsigned trace with contraction. Multiplication by the
alternating sign cancels the degree sign because `k + k*k = k*(k+1)` is even.
The result includes degree zero and the zero-dimensional vector space. -/
theorem dold_signed_trace_eq_contraction
    (V : Type u) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (k : ℕ) (a : Module.Dual ℚ V ⊗[ℚ] V) :
    (-1 : ℚ)^k * LinearMap.trace ℚ V
      ((-1 : ℚ)^(k*k) • dualTensorHom ℚ V V a) = contractLeft ℚ V a := by
  rw [map_smul, smul_eq_mul, LinearMap.trace_eq_contract_apply]
  rw [← mul_assoc, ← pow_add]
  have heven : Even (k + k * k) := by
    rcases Nat.even_or_odd k with hk | hk
    · exact hk.add (hk.mul_right k)
    · exact hk.add_odd (hk.mul hk)
  rw [heven.neg_one_pow, one_mul]

/-- A finite family of Dold signed tensor maps has alternating trace equal to the
sum of tensor evaluations. Apply the degreewise contraction identity to every
summand; this is the finite graded algebra in Dold (3.2)–(3.4). -/
theorem dold_alternating_trace_eq_contraction_sum
    (V : ℕ → Type u) [∀ k, AddCommGroup (V k)] [∀ k, Module ℚ (V k)]
    [∀ k, FiniteDimensional ℚ (V k)]
    (s : Finset ℕ) (a : ∀ k, Module.Dual ℚ (V k) ⊗[ℚ] V k)
    (T : ∀ k, V k →ₗ[ℚ] V k)
    (hT : ∀ k ∈ s, T k = (-1 : ℚ)^(k*k) • dualTensorHom ℚ (V k) (V k) (a k)) :
    (∑ k ∈ s, (-1 : ℚ)^k * LinearMap.trace ℚ (V k) (T k)) =
      ∑ k ∈ s, contractLeft ℚ (V k) (a k) := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [hT k hk]
  exact dold_signed_trace_eq_contraction (V k) k (a k)

end HolomorphicAnosov
