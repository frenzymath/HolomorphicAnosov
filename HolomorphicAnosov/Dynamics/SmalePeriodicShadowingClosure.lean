import HolomorphicAnosov.Dynamics.SmalePeriodicClosureNonwandering
import Mathlib.Tactic.Linarith

/-! Periodic shadowing identifies the closure of periodic points with the nonwandering set (Shub,
Props. 1.7 and 8.5). -/

namespace HolomorphicAnosov

open Set

/-- If finite cyclic pseudo-orbits have periodic shadowers with arbitrarily small initial-point
error, the closure of periodic points equals the nonwandering set (Shub, Props. 1.7 and 8.5). -/
theorem smale_closure_periodic_eq_nonwandering_of_periodic_shadowing
    {X : Type*} [MetricSpace X] (f : X → X)
    (hshadow : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ), 0 < n → ∀ q : ℕ → X, q n = q 0 →
        (∀ k < n, dist (f (q k)) (q (k + 1)) < δ) →
        ∃ p : X, Function.IsPeriodicPt f n p ∧ dist p (q 0) < ε) :
    closure (Function.periodicPts f) =
      {x | ∀ U : Set X, IsOpen U → x ∈ U →
        ∃ k : ℕ, 0 < k ∧ (f^[k] '' U ∩ U).Nonempty} := by
  apply Subset.antisymm (smale_closure_periodicPts_subset_nonwandering f)
  intro x hx
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hshadowδ⟩ := hshadow (ε / 2) (by linarith)
  let r := min (ε / 2) (δ / 2)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  obtain ⟨n, hn, z, ⟨y, hy, rfl⟩, hfy⟩ :=
    hx (Metric.ball x r) Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hclose : dist (f^[n] y) y < δ := by
    have hy' : dist x y < δ / 2 := by
      rw [dist_comm]
      exact hy.trans_le (min_le_right _ _)
    have hfy' : dist (f^[n] y) x < δ / 2 := hfy.trans_le (min_le_right _ _)
    exact (dist_triangle _ x _).trans_lt (by linarith)
  let q : ℕ → X := fun k ↦ if k < n then f^[k] y else y
  have hq0 : q 0 = y := by simp [q, hn]
  have hqn : q n = q 0 := by simp [q, hn]
  have hjump : ∀ k < n, dist (f (q k)) (q (k + 1)) < δ := by
    intro k hk
    by_cases hkn : k + 1 < n
    · simp [q, hk, hkn, Function.iterate_succ_apply', hδ]
    · have hlast : k + 1 = n := by omega
      simpa [q, hk, hkn, ← Function.iterate_succ_apply', hlast] using hclose
  obtain ⟨p, hp, hpy⟩ := hshadowδ n hn q hqn hjump
  refine ⟨p, Function.mem_periodicPts.mpr ⟨n, hn, hp⟩, ?_⟩
  have hpx : dist p x < ε := by
    rw [hq0] at hpy
    have hy' : dist y x < ε / 2 := hy.trans_le (min_le_left _ _)
    exact (dist_triangle p y x).trans_lt (by linarith)
  simpa only [dist_comm] using hpx


end HolomorphicAnosov
