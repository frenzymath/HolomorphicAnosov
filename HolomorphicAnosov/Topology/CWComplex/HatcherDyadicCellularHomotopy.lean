import HolomorphicAnosov.Topology.CWComplex.StationarySkeletalHomotopy
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Order.OrderClosed

namespace HolomorphicAnosov.Topology.CWComplex

universe u v

/-- Hatcher, Algebraic Topology, proof of Theorem 4.8, p.349: perform the nth
skeletal homotopy in the interval [1-2^(-n),1-2^(-(n+1))]. Each point lies
in a skeleton on which all subsequent homotopies are stationary.

Construct the finite prefixes with these exact time slots, keeping each
prefix constant after its last slot. At the common time endpoint the two
formulas agree, so closed pasting gives continuity. The new stage is fixed
on every previously completed skeleton, hence appending it preserves the
entire earlier track there. The source's eventual-stationarity argument,
formalized by the public compatible-skeleton assembly theorem, then gives
a cellular endpoint and a homotopy relative to the actual subcomplex A. -/
theorem hatcher_dyadic_cellular_homotopy
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X)) (F : ℕ → C(X, Y))
    (G : ∀ n, ContinuousMap.HomotopyRel (F n) (F (n + 1)) (A : Set X))
    (hfixed : ∀ (n : ℕ) (t : unitInterval) x,
      x ∈ (Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X) →
      G (n + 1) (t, x) = F (n + 1) x)
    (hcell : ∀ n : ℕ, Set.MapsTo (F (n + 1))
      (Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X)
      (Topology.CWComplex.skeleton (Set.univ : Set Y) (n : ℕ∞) : Set Y)) :
    ∃ c : C(X, Y),
      (∀ n : ℕ, Set.MapsTo c
        (Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X)
        (Topology.CWComplex.skeleton (Set.univ : Set Y) (n : ℕ∞) : Set Y)) ∧
      Nonempty (ContinuousMap.HomotopyRel (F 0) c (A : Set X)) := by
  let tau : ℕ → ℝ := fun n ↦ 1 - (1 / 2 : ℝ) ^ n
  have hnonneg (n : ℕ) : 0 ≤ tau n :=
    sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))
  have hstrict (n : ℕ) : tau n < tau (n + 1) := by
    dsimp [tau]
    rw [pow_succ]
    have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) _
    linarith
  have hle (n : ℕ) : tau n ≤ 1 := sub_le_self _ (pow_nonneg (by norm_num) _)
  let P (n : ℕ) := {H : ContinuousMap.HomotopyRel (F 0) (F n) (A : Set X) //
    ∀ (t : unitInterval) x, tau n ≤ (t : ℝ) → H (t, x) = F n x}
  let start : P 0 := ⟨ContinuousMap.HomotopyRel.refl (F 0) (A : Set X),
    fun _ _ _ ↦ rfl⟩
  let step (n : ℕ) (H : P n) : P (n + 1) := by
    have hden : 0 < tau (n + 1) - tau n := sub_pos.mpr (hstrict n)
    refine ⟨{
      toFun := fun z ↦ if (z.1 : ℝ) ≤ tau n then H.val z
        else (G n).toHomotopy.extend (((z.1 : ℝ) - tau n) / (tau (n + 1) - tau n)) z.2
      continuous_toFun := continuous_if_le (by fun_prop) continuous_const
        H.val.continuous.continuousOn
        ((G n).continuous.comp (by fun_prop)).continuousOn (by
          intro z hz
          simp only [hz, sub_self, zero_div]
          exact (H.property z.1 z.2 hz.ge).trans
            ((G n).toHomotopy.extend_apply_of_le_zero le_rfl z.2).symm)
      map_zero_left := by
        intro x
        simp [hnonneg]
      map_one_left := by
        intro x
        have hn1 : tau n < 1 := (hstrict n).trans_le (hle _)
        change (if (1 : ℝ) ≤ tau n then _ else _) = _
        rw [ite_eq_right (not_le.mpr hn1)]
        change (G n).toHomotopy.extend ((1 - tau n) / (tau (n + 1) - tau n)) x = _
        exact (G n).toHomotopy.extend_apply_of_one_le
          ((le_div_iff₀ hden).mpr (by linarith [hle (n + 1)])) x
      prop' := by
        intro t x hx
        change (if (t : ℝ) ≤ tau n then _ else _) = _
        split_ifs with ht
        · exact H.val.eq_fst t hx
        · exact ((G n).extendProp _ x hx).trans (H.val.fst_eq_snd hx).symm }, ?_⟩
    intro t x ht
    have hnt : ¬ (t : ℝ) ≤ tau n := not_le.mpr ((hstrict n).trans_le ht)
    change (if (t : ℝ) ≤ tau n then _ else _) = _
    rw [ite_eq_right hnt]
    exact (G n).toHomotopy.extend_apply_of_one_le
      ((le_div_iff₀ hden).mpr (by linarith)) x
  let seq : ∀ n, P n := Nat.rec start step
  have htracks (n : ℕ) (t : unitInterval) (x : X)
      (hx : x ∈ (Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X)) :
      (seq (n + 2)).val (t, x) = (seq (n + 1)).val (t, x) := by
    change (if (t : ℝ) ≤ tau (n + 1) then _ else _) = _
    split_ifs with ht
    · rfl
    · rw [(seq (n + 1)).property t x (le_of_not_ge ht)]
      exact hfixed n _ x hx
  obtain ⟨c, hc, H, _⟩ := stationary_skeletal_cellular_homotopy (A : Set X) (F 0)
    (fun n ↦ F (n + 1)) (fun n ↦ (seq (n + 1)).val) htracks hcell
  exact ⟨c, hc, ⟨H⟩⟩

end HolomorphicAnosov.Topology.CWComplex
