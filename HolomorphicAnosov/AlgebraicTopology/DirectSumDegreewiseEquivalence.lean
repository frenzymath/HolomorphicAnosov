import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Finite-support degreewise equivalences on graded direct sums

Given linear equivalences on every total-degree fibre of a tensor of graded
modules, this module assembles them into one linear equivalence on the tensor
of the two graded direct sums.  The construction is the finite-support
reindexing used in Hatcher's cohomological cross-product proof (pp. 215–218).
-/

noncomputable section

open scoped TensorProduct DirectSum

universe u

namespace HolomorphicAnosov.AlgebraicTopology

variable (R : Type u) [CommRing R]

/-- Reindex a direct sum by the fibres of a degree map, preserving its
R-linear structure. -/
def sigmaFiberLinearEquiv (d : (ℕ × ℕ) → ℕ) (B : (ℕ × ℕ) → Type u)
    [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)] :
    (⨁ i, B i) ≃ₗ[R] ⨁ k, ⨁ i : {i : ℕ × ℕ // d i = k}, B i := by
  let e := DirectSum.sigmaFiberAddEquiv d (β := B)
  exact {
    toAddEquiv := e
    map_smul' := fun r x ↦ by
      ext k i
      change (r • x) i.val = r • x i.val
      exact DFinsupp.smul_apply r x i.val }

/-- Assemble degreewise tensor equivalences into an equivalence of the total
graded direct sums.  The generator formula is literal on every pure tensor. -/
theorem total_equiv_of_degree_equivs
    (A B C : ℕ → Type u) [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    (e : ∀ k, (⨁ i : {i : ℕ × ℕ // i.1 + i.2 = k},
      A i.val.1 ⊗[R] B i.val.2) ≃ₗ[R] C k) :
    ∃ μ : ((⨁ n, A n) ⊗[R] (⨁ n, B n)) ≃ₗ[R] ⨁ n, C n,
      ∀ p q (a : A p) (b : B q),
        μ ((DirectSum.lof R ℕ A p a) ⊗ₜ[R] (DirectSum.lof R ℕ B q b)) =
          DirectSum.lof R ℕ C (p + q)
            (e (p + q) (DirectSum.lof R _ _ ⟨(p, q), rfl⟩ (a ⊗ₜ[R] b))) := by
  classical
  let dist := TensorProduct.directSum R R A B
  let group := sigmaFiberLinearEquiv R (fun i : ℕ × ℕ ↦ i.1 + i.2)
    (fun i : ℕ × ℕ ↦ A i.1 ⊗[R] B i.2)
  let μ := (dist.trans group).trans (DirectSum.congrLinearEquiv e)
  refine ⟨μ, ?_⟩
  intro p q a b
  change DirectSum.congrLinearEquiv e (group (dist (_ ⊗ₜ[R] _))) = _
  simp only [dist, TensorProduct.directSum_lof_tmul_lof]
  change DirectSum.congrLinearEquiv e
    (DirectSum.sigmaFiberAddEquiv (fun i : ℕ × ℕ ↦ i.1 + i.2)
      (DirectSum.of (fun i : ℕ × ℕ ↦ A i.1 ⊗[R] B i.2) (p, q) (a ⊗ₜ[R] b))) = _
  rw [DirectSum.sigmaFiberAddEquiv_of]
  exact DirectSum.lmap_lof (fun k ↦ (e k).toLinearMap) _ _


end HolomorphicAnosov.AlgebraicTopology
