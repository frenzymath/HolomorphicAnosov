import Mathlib.Geometry.Manifold.Riemannian.PathELength

open Set
open scoped Manifold ContDiff Bundle

namespace HolomorphicAnosov

/-! Riemannian extended path length is additive over finite ordered partitions. -/

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, ENorm (TangentSpace I x)]

/-- The sum of the Riemannian extended lengths over consecutive intervals of an ordered partition
equals the length over the whole interval. (Lee, p.275) -/
theorem sum_pathELength_partition
    {γ : ℝ → M} (d : ℕ → ℝ) (hd : Monotone d) (N : ℕ) :
    ∑ i : Fin N, Manifold.pathELength I γ (d i) (d (i + 1)) =
      Manifold.pathELength I γ (d 0) (d N) := by
  induction N generalizing d with
  | zero => simp
  | succ N ih =>
      rw [Fin.sum_univ_succ]
      have htail := ih (fun j => d (j + 1))
        (fun j k hjk => hd (Nat.add_le_add_right hjk 1))
      have htail' : (∑ i : Fin N,
          Manifold.pathELength I γ (d i.succ) (d (i.succ + 1))) =
          Manifold.pathELength I γ (d 1) (d (N + 1)) := by
        simpa [Nat.succ_eq_add_one] using htail
      rw [htail']
      calc
        _ = Manifold.pathELength I γ (d 0) (d (N + 1)) := by
          simpa using (Manifold.pathELength_add (I := I) (γ := γ)
            (a := d 0) (b := d 1) (c := d (N + 1))
            (hd (Nat.zero_le 1)) (hd (Nat.succ_le_succ (Nat.zero_le N))))
        _ = _ := by simp

end HolomorphicAnosov

