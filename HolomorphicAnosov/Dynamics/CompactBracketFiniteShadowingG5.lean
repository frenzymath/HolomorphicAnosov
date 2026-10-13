import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Finite shadowing from contracting local products

Shub, Global Stability of Dynamical Systems (1987), Proposition 8.20,
pp.109–110. Correct each successive image by its stable/unstable bracket.
Uniform continuity of the bracket on a compact neighborhood of the diagonal
makes the unstable correction small; stable contraction preserves the chosen
stable radius. Pulling corrections backward gives a geometric bound.
-/
namespace HolomorphicAnosov
open Set

/-- The local-product correction construction shadows every finite segment.

Choose a stable radius r smaller than the requested error and the bracket
radius. On pairs at distance at most half the bracket radius the bracket is
uniformly continuous. Thus replacing the first entry by a sufficiently close
point changes the bracket by at most c=(1-lambda)r/4. If y is in the stable
core of x and dist(y,x)≤r, the bracket of (x,y) is y; after advancing one
step its stable distance is at most lambda r. Bracketing with the next
pseudo-orbit point changes it by less than c. The triangle inequality keeps
its new stable distance at most r. The change lies in the unstable core, so
pulling it back k steps multiplies its distance by at most lambda^k.
The geometric sum is bounded by c/(1-lambda)=r/4. Pull back the final
corrected point: at each earlier time it differs from that time's corrected
point by at most r/4, and hence from the pseudo-orbit by less than the
requested error. All choices precede the segment length. -/
theorem compact_bracket_finite_shadowing_g5
    {X : Type*} [MetricSpace X] [CompactSpace X] (f : X ≃ₜ X)
    (γ ε rate : ℝ) (hγ : 0 < γ) (hε : 0 < ε) (hrate : 0 ≤ rate) (hrate1 : rate < 1)
    (b : X × X → X)
    (hb : ContinuousOn b {p | dist p.1 p.2 < ε})
    (hbr : ∀ x y, dist x y < ε →
      {z | ∀ n : ℕ, dist ((f : X → X)^[n] z) ((f : X → X)^[n] x) ≤ γ} ∩
      {z | ∀ n : ℕ, dist ((f.symm : X → X)^[n] z) ((f.symm : X → X)^[n] y) ≤ γ}
        = {b (x, y)})
    (hs : ∀ x y, (∀ n : ℕ, dist ((f : X → X)^[n] y) ((f : X → X)^[n] x) ≤ γ) →
      ∀ n : ℕ, dist ((f : X → X)^[n] y) ((f : X → X)^[n] x) ≤ rate^n * dist y x)
    (hu : ∀ x y, (∀ n : ℕ, dist ((f.symm : X → X)^[n] y)
      ((f.symm : X → X)^[n] x) ≤ γ) →
      ∀ n : ℕ, dist ((f.symm : X → X)^[n] y) ((f.symm : X → X)^[n] x) ≤ rate^n * dist y x) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ q : ℕ → X, (∀ i, dist (f (q i)) (q (i + 1)) < δ) →
      ∀ N : ℕ, ∃ a : X, ∀ i ≤ N, dist ((f : X → X)^[i] a) (q i) < η := by
  intro η hη
  let r : ℝ := min (η / 4) (ε / 8)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hrη : r ≤ η / 4 := min_le_left _ _
  have hrε : r ≤ ε / 8 := min_le_right _ _
  let c : ℝ := (1 - rate) * r / 4
  have hc : 0 < c := by dsimp [c]; positivity
  let K : Set (X × X) := {p | dist p.1 p.2 ≤ ε / 2}
  have hK : IsCompact K := (isClosed_le (continuous_fst.dist continuous_snd)
    continuous_const).isCompact
  have huB : UniformContinuousOn b K := hK.uniformContinuousOn_of_continuous
    (hb.mono (fun p hp ↦ by dsimp [K] at hp; dsimp; linarith))
  obtain ⟨d, hd, hmod⟩ := Metric.uniformContinuousOn_iff.mp huB c hc
  let δ : ℝ := min d (min c (ε / 8))
  have hδ : 0 < δ := lt_min hd (lt_min hc (by linarith))
  have hδd : δ ≤ d := min_le_left _ _
  have hδc : δ ≤ c := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ ≤ ε / 8 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, ?_⟩
  intro q hq
  let y : ℕ → X := fun n ↦ Nat.rec (q 0) (fun i z ↦ b (q (i + 1), f z)) n
  have hy0 : y 0 = q 0 := rfl
  have hys (i : ℕ) : y (i + 1) = b (q (i + 1), f (y i)) := rfl
  have hy : ∀ i, (∀ n : ℕ, dist ((f : X → X)^[n] (y i))
      ((f : X → X)^[n] (q i)) ≤ γ) ∧ dist (y i) (q i) ≤ r ∧
      (∀ n : ℕ, dist ((f.symm : X → X)^[n] (y (i + 1)))
        ((f.symm : X → X)^[n] (f (y i))) ≤ γ) ∧
        dist (y (i + 1)) (f (y i)) < c := by
    have step (i : ℕ)
        (hstable : ∀ n : ℕ, dist ((f : X → X)^[n] (y i))
          ((f : X → X)^[n] (q i)) ≤ γ) (hclose : dist (y i) (q i) ≤ r) :
        (∀ n : ℕ, dist ((f : X → X)^[n] (y (i + 1)))
          ((f : X → X)^[n] (q (i + 1))) ≤ γ) ∧
        dist (y (i + 1)) (q (i + 1)) ≤ r ∧
        (∀ n : ℕ, dist ((f.symm : X → X)^[n] (y (i + 1)))
          ((f.symm : X → X)^[n] (f (y i))) ≤ γ) ∧
        dist (y (i + 1)) (f (y i)) < c := by
      have hfclose : dist (f (y i)) (f (q i)) ≤ rate * r := by
        have hh : dist (f (y i)) (f (q i)) ≤ rate * dist (y i) (q i) := by
          simpa using hs _ _ hstable 1
        exact hh.trans
          (mul_le_mul_of_nonneg_left hclose hrate)
      have hrater : rate * r ≤ r := mul_le_of_le_one_left hr.le hrate1.le
      have hpair : dist (q (i + 1)) (f (y i)) < ε / 2 := by
        have htri := dist_triangle (q (i + 1)) (f (q i)) (f (y i))
        have hsym1 := dist_comm (q (i+1)) (f (q i))
        have hsym2 := dist_comm (f (q i)) (f (y i))
        have hh := (hq i).trans_le hδε
        linarith
      have hbase : b (f (q i), f (y i)) = f (y i) := by
        apply (Set.mem_singleton_iff.mp ?_).symm
        rw [← hbr _ _ (by rw [dist_comm]; linarith : dist (f (q i)) (f (y i)) < ε)]
        constructor
        · intro n
          simpa only [← Function.iterate_succ_apply] using hstable (n + 1)
        · intro n; simpa using hγ.le
      have hcorrection : dist (y (i + 1)) (f (y i)) < c := by
        rw [hys]
        conv_lhs => arg 2; rw [← hbase]
        apply hmod (q (i + 1), f (y i)) hpair.le
          (f (q i), f (y i)) (by dsimp [K]; rw [dist_comm]; linarith)
        simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg), dist_comm]
          using (hq i).trans_le hδd
      have hmem : (∀ n : ℕ, dist ((f : X → X)^[n] (y (i + 1)))
          ((f : X → X)^[n] (q (i + 1))) ≤ γ) ∧
          (∀ n : ℕ, dist ((f.symm : X → X)^[n] (y (i + 1)))
          ((f.symm : X → X)^[n] (f (y i))) ≤ γ) := by
        have heq := hbr (q (i+1)) (f (y i)) (by linarith : dist (q (i+1)) (f (y i)) < ε)
        rw [← hys] at heq
        have hh : y (i+1) ∈
            {z | ∀ n : ℕ, dist ((f : X → X)^[n] z) ((f : X → X)^[n] (q (i+1))) ≤ γ} ∩
            {z | ∀ n : ℕ, dist ((f.symm : X → X)^[n] z)
              ((f.symm : X → X)^[n] (f (y i))) ≤ γ} := by
          rw [heq]; exact Set.mem_singleton _
        exact hh
      refine ⟨hmem.1, ?_, hmem.2, hcorrection⟩
      have htri := dist_triangle (y (i+1)) (f (y i)) (q (i+1))
      have htri2 := dist_triangle (f (y i)) (f (q i)) (q (i+1))
      have hh := (hq i).trans_le hδc
      dsimp [c] at hcorrection hh
      nlinarith
    have hcore : ∀ i, (∀ n : ℕ, dist ((f : X → X)^[n] (y i))
        ((f : X → X)^[n] (q i)) ≤ γ) ∧ dist (y i) (q i) ≤ r := by
      intro i
      induction i with
      | zero => exact ⟨fun n ↦ by simp [hy0, hγ.le], by simpa [hy0] using hr.le⟩
      | succ i ih => exact ⟨(step i ih.1 ih.2).1, (step i ih.1 ih.2).2.1⟩
    intro i
    exact ⟨(hcore i).1, (hcore i).2, (step i (hcore i).1 (hcore i).2).2.2⟩
  have hpull : ∀ k i : ℕ, dist ((f.symm : X → X)^[k] (y (i+k))) (y i) ≤
      r / 4 * (1 - rate^k) := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      intro i
      have hback := hu (f (y (i+k))) (y (i+k+1)) (hy (i+k)).2.2.1 (k+1)
      have hstep : dist ((f.symm : X → X)^[k+1] (y (i+k+1)))
          ((f.symm : X → X)^[k] (y (i+k))) ≤ rate^(k+1) * c := by
        have heq : (f.symm : X → X)^[k+1] (f (y (i+k))) =
            (f.symm : X → X)^[k] (y (i+k)) := by
          rw [Function.iterate_succ_apply, f.symm_apply_apply]
        rw [heq] at hback
        exact hback.trans (mul_le_mul_of_nonneg_left (hy (i+k)).2.2.2.le (pow_nonneg hrate _))
      have htri := dist_triangle ((f.symm : X → X)^[k+1] (y (i+k+1)))
        ((f.symm : X → X)^[k] (y (i+k))) (y i)
      have hpow : 0 ≤ rate^k := pow_nonneg hrate _
      have hcrate : rate * c ≤ c := mul_le_of_le_one_left hc.le hrate1.le
      have hstep' : rate^(k+1) * c ≤ rate^k * c := by
        rw [pow_succ]; nlinarith
      have hind := ih i
      have hsmallstep := hstep.trans hstep'
      change dist ((f.symm : X → X)^[k+1] (y (i+k+1)))
        ((f.symm : X → X)^[k] (y (i+k))) ≤ rate^k * ((1-rate)*r/4) at hsmallstep
      change dist ((f.symm : X → X)^[k+1] (y (i+k+1))) (y i) ≤
        r / 4 * (1 - rate^(k+1))
      rw [pow_succ]
      nlinarith
  intro N
  refine ⟨(f.symm : X → X)^[N] (y N), ?_⟩
  intro i hi
  have horbit : (f : X → X)^[i] ((f.symm : X → X)^[N] (y N)) =
      (f.symm : X → X)^[N-i] (y N) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [Function.iterate_add_apply]
    have hcancel : (f : X → X)^[i] ((f.symm : X → X)^[i]
        ((f.symm : X → X)^[k] (y (i+k)))) = (f.symm : X → X)^[k] (y (i+k)) :=
      (Function.LeftInverse.iterate f.apply_symm_apply i) _
    simpa using hcancel
  rw [horbit]
  have hh := hpull (N-i) i
  rw [Nat.add_sub_of_le hi] at hh
  have htri := dist_triangle ((f.symm : X → X)^[N-i] (y N)) (y i) (q i)
  have hbound := (hy i).2.1
  have hpow := pow_nonneg hrate (N-i)
  nlinarith

/-- Compactness upgrades uniform finite-segment shadowing of infinite forward
pseudo-orbits to shadowing at every integer time. Shub (1987), Proposition
8.20, p.109: center a length 2N segment at time zero. Its closed error sets
are nonempty, nested and compact, so their intersection is nonempty. -/
theorem compact_full_shadowing_of_forward_segments_g5
    {X : Type*} [MetricSpace X] [CompactSpace X] (f : X ≃ₜ X)
    (hf : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ q : ℕ → X, (∀ i, dist (f (q i)) (q (i+1)) < δ) →
      ∀ N : ℕ, ∃ a : X, ∀ i ≤ N, dist ((f : X → X)^[i] a) (q i) < η) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ q : ℤ → X, (∀ i, dist (f (q i)) (q (i+1)) < δ) →
      ∃ a : X, ∀ i : ℤ, dist ((f.toEquiv ^ i) a) (q i) ≤ η := by
  intro η hη
  obtain ⟨δ, hδ, hfinite⟩ := hf η hη
  refine ⟨δ, hδ, ?_⟩
  intro q hq
  have hcont : ∀ k : ℤ, Continuous (fun x ↦ (f.toEquiv ^ k) x) := by
    intro k
    exact zpow_induction_left (P := fun g : Equiv.Perm X ↦ Continuous (g : X → X))
      continuous_id (fun g hg ↦ f.continuous.comp hg)
      (fun g hg ↦ f.symm.continuous.comp hg) k
  let K : ℕ → Set X := fun N ↦ {a | ∀ k : ℤ, -(N:ℤ) ≤ k → k ≤ N →
    dist ((f.toEquiv ^ k) a) (q k) ≤ η}
  have hclosed : ∀ N, IsClosed (K N) := by
    intro N
    simp only [K, ofPred_forall]
    exact isClosed_iInter fun k ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦
      isClosed_le ((hcont k).dist continuous_const) continuous_const
  have hnonempty : ∀ N, (K N).Nonempty := by
    intro N
    let qN : ℕ → X := fun i ↦ q ((i:ℤ)-N)
    obtain ⟨a, ha⟩ := hfinite qN
      (fun i ↦ by simpa [qN, Nat.cast_add, Nat.cast_one, sub_add_eq_add_sub] using hq ((i:ℤ)-N)) (2*N)
    refine ⟨(f : X → X)^[N] a, ?_⟩
    intro k hlo hhi
    let j : ℕ := (k+N).toNat
    have hj : (j:ℤ) = k+N := Int.toNat_of_nonneg (by omega)
    have hjbound : j ≤ 2*N := by omega
    have horbit : (f.toEquiv ^ k) ((f : X → X)^[N] a) =
        (f : X → X)^[j] a := by
      change (f.toEquiv ^ k) ((f.toEquiv ^ N) a) = (f.toEquiv ^ j) a
      rw [← zpow_natCast f.toEquiv N, ← zpow_natCast f.toEquiv j,
        ← Equiv.Perm.mul_apply, ← zpow_add, hj]
    rw [horbit]
    have hqN : qN j = q k := by simp [qN, hj]
    exact le_of_lt (hqN ▸ ha j hjbound)
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K
    (fun N a ha k hlo hhi ↦ ha k (by omega) (by omega)) hnonempty
    (hclosed 0).isCompact hclosed
  refine ⟨a, fun k ↦ (mem_iInter.mp ha k.natAbs) k (by omega) (by omega)⟩

/-- Shadowing and expansivity make every finite cyclic pseudo-orbit shadowable
by a cyclic orbit of the same length. Shub (1987), Proposition 8.5, p.103.
Extend the indexed pseudo-orbit periodically to integer time, keeping repeated
values as distinct indices. The point at time n and the point at time zero
shadow the same integer sequence. Expansivity identifies them. -/
theorem cyclic_shadowing_of_full_shadowing_expansive_g5
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X)
    (γ : ℝ) (hγ : 0 < γ)
    (hexp : ∀ x y, (∀ k : ℤ, dist ((f.toEquiv^k) x) ((f.toEquiv^k) y) ≤ γ) → x = y)
    (hfull : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ q : ℤ → X, (∀ i, dist (f (q i)) (q (i+1)) < δ) →
      ∃ a : X, ∀ i : ℤ, dist ((f.toEquiv ^ i) a) (q i) ≤ η) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ, 0 < n → ∀ q : Fin n → X,
      (∀ i, dist (f (q i)) (q (finRotate n i)) < δ) →
      ∃ j : Fin n → X, Function.Semiconj j (finRotate n) f ∧
        ∀ i, dist (j i) (q i) ≤ η := by
  classical
  intro η hη
  let c := min η (γ / 4)
  have hc : 0 < c := lt_min hη (by linarith)
  obtain ⟨δ, hδ, hf⟩ := hfull c hc
  refine ⟨δ, hδ, ?_⟩
  intro n hn q hq
  let : NeZero n := ⟨by omega⟩
  have hrotiter : ∀ k : ℕ, ∀ i : Fin n, (finRotate n)^[k] i = i + Fin.ofNat n k := by
    intro k i
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, finRotate_apply]
      open scoped Fin.NatCast in
      change (i + (k : Fin n)) + 1 = i + ((k+1 : ℕ) : Fin n)
      simp [Nat.cast_add, Nat.cast_one, add_assoc]
  have hrotpow : (finRotate n)^n = 1 := by
    apply Equiv.ext
    intro i
    change (finRotate n)^[n] i = i
    rw [hrotiter]
    simp
  let Q : ℤ → X := fun k ↦ q (((finRotate n)^k) 0)
  have hQjump : ∀ k, dist (f (Q k)) (Q (k+1)) < δ := by
    intro k
    have heq : ((finRotate n)^(k+1)) 0 = finRotate n (((finRotate n)^k) 0) := by
      rw [add_comm k 1, zpow_add, zpow_one, Equiv.Perm.mul_apply]
    simpa only [Q, heq] using hq (((finRotate n)^k) 0)
  obtain ⟨a, ha⟩ := hf Q hQjump
  have hQperiod : ∀ k, Q (k+(n:ℤ)) = Q k := by
    intro k
    simp only [Q, zpow_add, zpow_natCast, hrotpow, mul_one]
  have hperiod : (f.toEquiv^n) a = a := by
    apply hexp
    intro k
    have h1 := ha (k+(n:ℤ))
    rw [hQperiod, zpow_add, zpow_natCast, Equiv.Perm.mul_apply] at h1
    have h2 := ha k
    have ht := dist_triangle ((f.toEquiv^k) ((f.toEquiv^n) a)) (Q k) ((f.toEquiv^k) a)
    rw [dist_comm (Q k)] at ht
    have hcγ : c ≤ γ / 4 := min_le_right _ _
    linarith
  let j : Fin n → X := fun i ↦ (f.toEquiv^i.val) a
  have hsem : Function.Semiconj j (finRotate n) f := by
    intro i
    have hval : (finRotate n i).val = (i.val + 1) % n := by
      rw [finRotate_apply]; simp [Fin.val_add]
    by_cases hi : i.val + 1 < n
    · change (f.toEquiv ^ (finRotate n i).val) a = f ((f.toEquiv^i.val) a)
      rw [hval, Nat.mod_eq_of_lt hi, pow_succ', Equiv.Perm.mul_apply]
      rfl
    · have heq : i.val + 1 = n := by omega
      change (f.toEquiv ^ (finRotate n i).val) a = f ((f.toEquiv^i.val) a)
      rw [hval, heq, Nat.mod_self, pow_zero, Equiv.Perm.one_apply]
      have hh : (f.toEquiv^(i.val+1)) a = a := by simpa only [heq] using hperiod
      rw [pow_succ', Equiv.Perm.mul_apply] at hh
      exact hh.symm
  refine ⟨j, hsem, ?_⟩
  intro i
  have hQi : Q (i.val:ℤ) = q i := by
    simp only [Q, zpow_natCast, Equiv.Perm.coe_pow, hrotiter, zero_add]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hh := ha (i.val:ℤ)
  rw [hQi, zpow_natCast] at hh
  exact hh.trans (min_le_left _ _)

end HolomorphicAnosov

