import Mathlib.Geometry.Manifold.Riemannian.PathELength

namespace HolomorphicAnosov

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [∀ x : M, ENorm (TangentSpace I x)]
variable [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]

/-- Riemannian extended distance between the endpoints of a finite chain is bounded by the sum of
the extended distances along the chain. -/
theorem riemannianEDist_le_fin_chain :
    ∀ n : ℕ, ∀ a b : Fin (n + 1) → M,
      (∀ i : Fin n, b i.castSucc = a i.succ) →
      Manifold.riemannianEDist I (a 0) (b (Fin.last n)) ≤
        ∑ i, Manifold.riemannianEDist I (a i) (b i) := by
  intro n
  induction n with
  | zero => intro a b hj; simp
  | succ n ih =>
    intro a b hj
    rw [Fin.sum_univ_succ]
    have ht := ih (fun i ↦ a i.succ) (fun i ↦ b i.succ)
      (fun i ↦ hj i.succ)
    calc
      _ ≤ Manifold.riemannianEDist I (a 0) (b 0) +
          Manifold.riemannianEDist I (b 0) (b (Fin.last (n + 1))) :=
        Manifold.riemannianEDist_triangle
      _ ≤ _ := by
        apply add_le_add_right
        have hzero : b 0 = a (Fin.succ 0) := by simpa using hj 0
        rw [hzero]
        exact ht

end HolomorphicAnosov
