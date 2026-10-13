import HolomorphicAnosov.Topology.TorusLefschetzPrincipalMinors
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

open scoped BigOperators
noncomputable section
universe u
namespace HolomorphicAnosov

/-- Convert the principal-minor diagonal coefficients in the degreewise torus
homology bases to the ordinary alternating trace.

Source: steps 4 and 6 of `topo.original_torus_lefschetz_determinant_g7`.
The trace in each basis is the sum of its diagonal coefficients, indexed by the
subsets of cardinality `k`. Reindex that sum as `powersetCard k` and apply the
proved alternating principal-minor identity. The diagonal coefficient premise
is precisely the cup-product calculation; this lemma does not assume the final
trace or determinant equality. No invertibility or positive dimension is needed. -/
theorem torus_lefschetz_trace_of_minor_diagonals (n : ℕ)
    (B : Matrix (Fin n) (Fin n) ℚ)
    (V : ℕ → Type u) [∀ k, AddCommGroup (V k)] [∀ k, Module ℚ (V k)]
    (b : ∀ k, Module.Basis {S : Finset (Fin n) // S.card = k} ℚ (V k))
    (f : ∀ k, V k →ₗ[ℚ] V k)
    (hdiag : ∀ k (S : {S : Finset (Fin n) // S.card = k}),
      (b k).repr (f k (b k S)) S =
        (B.submatrix (Subtype.val : S.val → Fin n)
          (Subtype.val : S.val → Fin n)).det) :
    (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * LinearMap.trace ℚ (V k) (f k)) =
      Matrix.det (1 - B) := by
  classical
  rw [← torus_lefschetz_alternating_principal_minors n B]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [LinearMap.trace_eq_matrix_trace ℚ (b k), Matrix.trace]
  simp_rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hdiag]
  exact (Finset.sum_subtype (Finset.univ.powersetCard k)
    (fun S ↦ by simp [Finset.mem_powersetCard])
    (fun S : Finset (Fin n) ↦
      (B.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det)).symm



end HolomorphicAnosov
