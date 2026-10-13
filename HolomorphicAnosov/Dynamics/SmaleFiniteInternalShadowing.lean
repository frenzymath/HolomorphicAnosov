import HolomorphicAnosov.Dynamics.SmaleCyclicShadowing
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.Linarith

/-! Internal finite shadowing on invariant transitive sets uniformly isolated among periodic points
(Shub, Prop. 8.20). -/

namespace HolomorphicAnosov
open Set Fin.NatCast

/-- An invariant transitive set uniformly isolated among periodic points has internal finite
shadowing whenever the ambient homeomorphism has cyclic shadowing. -/
theorem smale_finite_internal_shadowing_of_cyclic
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (A : Set X)
    (hinv : f '' A = A)
    (htrans : ∀ U V : Set X, IsOpen U → (U ∩ A).Nonempty →
      IsOpen V → (V ∩ A).Nonempty →
      ∃ k : ℕ, ((f : X → X)^[k] '' (U ∩ A) ∩ V).Nonempty)
    (hsep : ∃ η : ℝ, 0 < η ∧ ∀ a ∈ A, ∀ p ∈ Function.periodicPts (f : X → X),
      dist p a < η → p ∈ A)
    (hcyclic : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ), 0 < n → ∀ q : Fin n → X,
        (∀ i, dist (f (q i)) (q (finRotate n i)) < δ) →
        ∃ j : Fin n → X, Function.Semiconj j (finRotate n) f ∧
          ∀ i, dist (j i) (q i) < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ) (q : ℕ → X), (∀ k ≤ N, q k ∈ A) →
        (∀ k < N, dist (f (q k)) (q (k + 1)) < δ) →
        ∃ a ∈ A, ∀ k ≤ N, dist ((f : X → X)^[k] a) (q k) < ε := by
  classical
  obtain ⟨η, hη, hsep⟩ := hsep
  intro ε hε
  obtain ⟨δ, hδ, hshadow⟩ := hcyclic (min ε η) (lt_min hε hη)
  refine ⟨δ, hδ, ?_⟩
  intro N q hq hjump
  have hfqN : f (q N) ∈ A := by
    rw [← hinv]
    exact mem_image_of_mem f (hq N le_rfl)
  have hfiq0 : f.symm (q 0) ∈ A := by
    obtain ⟨x, hx, heq⟩ := hinv.symm ▸ hq 0 (Nat.zero_le N)
    simpa [← heq] using hx
  obtain ⟨k, z, ⟨a, ⟨haU, haA⟩, rfl⟩, haV⟩ :=
    htrans (Metric.ball (f (q N)) δ) (f ⁻¹' Metric.ball (q 0) δ)
      Metric.isOpen_ball ⟨f (q N), Metric.mem_ball_self hδ, hfqN⟩
      (Metric.isOpen_ball.preimage f.continuous)
      ⟨f.symm (q 0), by simpa using (Metric.mem_ball_self hδ : q 0 ∈ Metric.ball (q 0) δ), hfiq0⟩
  let T := N + k + 2
  have hT : 0 < T := by omega
  let : NeZero T := ⟨by omega⟩
  let Q : Fin T → X := fun i ↦ if i.val ≤ N then q i.val else
    (f : X → X)^[i.val - (N + 1)] a
  have hQ0 : Q 0 = q 0 := by simp [Q]
  have hQjump (i : Fin T) : dist (f (Q i)) (Q (finRotate T i)) < δ := by
    have hrot : (finRotate T i).val = (i.val + 1) % T := by
      rw [finRotate_apply]
      simp [Fin.val_add]
    by_cases hi : i.val < N
    · have hnext : i.val + 1 < T := by omega
      simp only [Q, hrot, Nat.mod_eq_of_lt hnext,
        ite_eq_left (by omega : i.val ≤ N), ite_eq_left (by omega : i.val + 1 ≤ N)]
      exact hjump i.val hi
    · by_cases hieq : i.val = N
      · have hnext : N + 1 < T := by omega
        simp only [Q, hrot, hieq, Nat.mod_eq_of_lt hnext, le_refl, ite_true,
          ite_eq_right (by omega : ¬N + 1 ≤ N), Nat.sub_self, Function.iterate_zero,
          id_eq]
        simpa only [dist_comm a (f (q N))] using (Metric.mem_ball.mp haU)
      · by_cases hlast : i.val + 1 = T
        · have hidx : i.val - (N + 1) = k := by dsimp [T] at hlast; omega
          simp only [Q, hrot, hlast, Nat.mod_self, Nat.zero_le, ite_true,
            ite_eq_right (by omega : ¬i.val ≤ N), hidx]
          exact haV
        · have hnext : i.val + 1 < T := by omega
          have hidx : i.val + 1 - (N + 1) = (i.val - (N + 1)) + 1 := by omega
          simp only [Q, hrot, Nat.mod_eq_of_lt hnext,
            ite_eq_right (by omega : ¬i.val ≤ N), ite_eq_right (by omega : ¬i.val + 1 ≤ N),
            hidx, Function.iterate_succ_apply', dist_self]
          exact hδ
  obtain ⟨j, hj, hclose⟩ := hshadow T hT Q hQjump
  have hiter (i : ℕ) : (f : X → X)^[i] (j 0) = j (i : Fin T) := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih, ← hj]
      congr 1
      simp [finRotate_apply, Nat.cast_add, Nat.cast_one]
  have hperiod : Function.IsPeriodicPt (f : X → X) T (j 0) := by
    exact show (f : X → X)^[T] (j 0) = j 0 from by
      simpa only [Fin.natCast_self] using hiter T
  have hjA : j 0 ∈ A := hsep (q 0) (hq 0 (Nat.zero_le N)) (j 0)
    (Function.mem_periodicPts.mpr ⟨T, hT, hperiod⟩)
    (by simpa only [hQ0] using (hclose 0).trans_le (min_le_right ε η))
  refine ⟨j 0, hjA, ?_⟩
  intro i hi
  have hiT : i < T := by omega
  have hQi : Q (i : Fin T) = q i := by
    simp [Q, Fin.val_natCast, Nat.mod_eq_of_lt hiT, hi]
  rw [hiter, ← hQi]
  exact (hclose _).trans_le (min_le_left ε η)

end HolomorphicAnosov

