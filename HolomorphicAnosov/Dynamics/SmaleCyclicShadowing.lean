import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Dynamics.PeriodicPts.Defs

/-! Periodic shadowing from semiconjugacies on finite cyclic index sets (Shub, Prop. 8.5). -/

namespace HolomorphicAnosov
open Fin.NatCast

/-- Cyclic shadowing semiconjugacies supply periodic shadowers of finite cyclic pseudo-orbits with
the prescribed period and initial-point accuracy (Shub, Prop. 8.5; Thm. 7.8). -/
theorem smale_periodic_shadowing_of_cyclic_semiconjugacy
    {X : Type*} [MetricSpace X] (f : X → X)
    (hcyclic : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ), 0 < n → ∀ q : Fin n → X,
        (∀ i, dist (f (q i)) (q (finRotate n i)) < δ) →
        ∃ j : Fin n → X, Function.Semiconj j (finRotate n) f ∧
          ∀ i, dist (j i) (q i) < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ), 0 < n → ∀ q : ℕ → X, q n = q 0 →
        (∀ k < n, dist (f (q k)) (q (k + 1)) < δ) →
        ∃ p : X, Function.IsPeriodicPt f n p ∧ dist p (q 0) < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hδcyclic⟩ := hcyclic ε hε
  refine ⟨δ, hδ, ?_⟩
  intro n hn q hqn hjump
  let : NeZero n := ⟨by omega⟩
  have hjump' (i : Fin n) : dist (f (q i.val)) (q (finRotate n i).val) < δ := by
    have hval : (finRotate n i).val = (i.val + 1) % n := by
      rw [finRotate_apply]
      simp [Fin.val_add]
    rw [hval]
    by_cases hi : i.val + 1 < n
    · rw [Nat.mod_eq_of_lt hi]
      exact hjump _ i.isLt
    · have hi' : i.val + 1 = n := by omega
      simpa [hi', hqn] using hjump i.val i.isLt
  obtain ⟨j, hj, hclose⟩ := hδcyclic n hn (fun i ↦ q i.val) hjump'
  have hiter (k : ℕ) : f^[k] (j 0) = j (k : Fin n) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, ← hj]
      congr 1
      simp [finRotate_apply, Nat.cast_add, Nat.cast_one]
  refine ⟨j 0, ?_, ?_⟩
  · exact show f^[n] (j 0) = j 0 from by simpa only [Fin.natCast_self] using hiter n
  · simpa using hclose 0


end HolomorphicAnosov
