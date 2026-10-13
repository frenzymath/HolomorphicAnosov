import Mathlib

/-! The endpoint displacement of a finite piecewise path is bounded by the sum of its piecewise
endpoint displacements. (Lee, §11, pp.275–279; Hirsch–Pugh–Shub, proof of Thm (6.7), p.86) -/

namespace HolomorphicAnosov

/-- The norm of the endpoint displacement of a finite chain with matching junctions is at most the
sum of the norms of its piecewise endpoint displacements. -/
theorem norm_sub_le_sum_norm_sub_junction
    {E : Type*} [NormedAddCommGroup E]
    (n : ℕ) (start finish : Fin (n + 1) → E)
    (hjunction : ∀ i : Fin n, finish i.castSucc = start i.succ) :
    ‖finish (Fin.last n) - start 0‖ ≤
      ∑ i : Fin (n + 1), ‖finish i - start i‖ := by
  have htel : (∑ i : Fin (n + 1), (finish i - start i)) =
      finish (Fin.last n) - start 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.sum_univ_succ]
      have hmid : finish 0 = start 1 := hjunction ⟨0, by omega⟩
      have hrest : (∑ i : Fin (n + 1),
          (finish i.succ - start i.succ)) =
          finish (Fin.last (n + 1)) - start 1 := by
        apply ih
        intro i
        exact hjunction i.succ
      rw [hrest, hmid]
      simp only [Fin.last]
      abel
  rw [← htel]
  simpa only using (norm_sum_le (Finset.univ : Finset (Fin (n + 1)))
    (fun i ↦ finish i - start i))

end HolomorphicAnosov

