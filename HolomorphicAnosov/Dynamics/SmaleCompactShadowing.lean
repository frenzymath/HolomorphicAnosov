import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Linarith

/-! Finite shadowing on a compact invariant set implies bi-infinite shadowing (Shub, Prop. 8.20). -/

namespace HolomorphicAnosov

open Set

/-- Internal shadowing of finite pseudo-orbit segments in a compact invariant set implies internal
shadowing of bi-infinite pseudo-orbits (Shub, Prop. 8.20). -/
theorem smale_shadowing_of_finite_shadowing
    {X : Type*} [MetricSpace X] (e : X ≃ₜ X) (A : Set X)
    (hA : IsCompact A) (hinv : e '' A = A)
    (hfinite : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ) (q : ℕ → X), (∀ k ≤ N, q k ∈ A) →
        (∀ k < N, dist (e (q k)) (q (k + 1)) < δ) →
        ∃ a ∈ A, ∀ k ≤ N, dist ((e : X → X)^[k] a) (q k) < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ q : ℤ → X, (∀ k, q k ∈ A) →
        (∀ k, dist (e (q k)) (q (k + 1)) < δ) →
        ∃ a ∈ A, ∀ k : ℤ, dist ((e.toEquiv ^ k) a) (q k) < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hδshadow⟩ := hfinite (ε / 2) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro q hq hjump
  have hiterA : ∀ (n : ℕ) {a}, a ∈ A → (e : X → X)^[n] a ∈ A := by
    intro n a ha
    induction n with
    | zero => exact ha
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [← hinv]
      exact mem_image_of_mem e ih
  have hcont : ∀ k : ℤ, Continuous (fun x ↦ (e.toEquiv ^ k) x) := by
    intro k
    exact zpow_induction_left (P := fun g : Equiv.Perm X ↦ Continuous (g : X → X))
      continuous_id (fun g hg ↦ e.continuous.comp hg)
      (fun g hg ↦ e.symm.continuous.comp hg) k
  let K : ℕ → Set X := fun N ↦
    A ∩ {a | ∀ k : ℤ, -(N : ℤ) ≤ k → k ≤ N →
      dist ((e.toEquiv ^ k) a) (q k) ≤ ε / 2}
  have hclosed : ∀ N, IsClosed (K N) := by
    intro N
    apply hA.isClosed.inter
    simp only [ofPred_forall]
    exact isClosed_iInter fun k ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦
      isClosed_le ((hcont k).dist continuous_const) continuous_const
  have hnonempty : ∀ N, (K N).Nonempty := by
    intro N
    let qN : ℕ → X := fun k ↦ q ((k : ℤ) - N)
    obtain ⟨a, ha, hshadow⟩ := hδshadow (2 * N) qN (fun k _ ↦ hq _)
      (fun k _ ↦ by
        simpa [qN, Nat.cast_add, Nat.cast_one, sub_add_eq_add_sub] using
          hjump ((k : ℤ) - N))
    refine ⟨(e : X → X)^[N] a, hiterA N ha, ?_⟩
    intro k hklo hkhi
    let j : ℕ := (k + N).toNat
    have hj : (j : ℤ) = k + N := Int.toNat_of_nonneg (by omega)
    have hjbound : j ≤ 2 * N := by omega
    have horbit : (e.toEquiv ^ k) ((e : X → X)^[N] a) =
        (e : X → X)^[j] a := by
      change (e.toEquiv ^ k) ((e.toEquiv ^ N) a) = (e.toEquiv ^ j) a
      rw [← zpow_natCast e.toEquiv N, ← zpow_natCast e.toEquiv j,
        ← Equiv.Perm.mul_apply, ← zpow_add, hj]
    rw [horbit]
    have hqN : qN j = q k := by simp [qN, hj]
    exact le_of_lt (hqN ▸ hshadow j hjbound)
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K
    (fun N a ha ↦ ⟨ha.1, fun k hklo hkhi ↦ ha.2 k (by omega) (by omega)⟩)
    hnonempty (hA.of_isClosed_subset (hclosed 0) inter_subset_left) hclosed
  refine ⟨a, (mem_iInter.mp ha 0).1, ?_⟩
  intro k
  have hk := (mem_iInter.mp ha k.natAbs).2 k (by omega) (by omega)
  linarith

end HolomorphicAnosov

