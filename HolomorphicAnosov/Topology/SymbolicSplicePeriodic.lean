import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding
import HolomorphicAnosov.Topology.SpliceAtInteger

namespace HolomorphicAnosov

open Set

/-- Every finite segment of a path whose adjacent pairs occur in the invariant splice
set is realized by one member of that same set. Manning Lemma 6, pp.427–428, invokes
Bowen's finite-type conclusion; this is its explicit finite-word induction. The induction
appends one witnessed edge, shifts its first symbol to the receiving seam, and applies
the guarded splice, preserving the entire previously realized past. -/
theorem finite_path_in_splice_set
    {S : Type*} (L : Set (ℤ → S))
    (hshift : ∀ a ∈ L, ∀ k : ℤ, SymbolicDynamics.FullShift.shift k a ∈ L)
    (hsplice : ∀ a ∈ L, ∀ b ∈ L, a 0 = b 0 →
      ∃ c ∈ L, (∀ j : ℤ, j ≤ 0 → c j = a j) ∧
        (∀ j : ℤ, 0 ≤ j → c j = b j))
    (b : ℤ → S)
    (hedge : ∀ k : ℤ, ∃ a ∈ L, a 0 = b k ∧ a 1 = b (k + 1))
    (l : ℤ) (t : ℕ) :
    ∃ a ∈ L, ∀ j : ℤ, 0 ≤ j → j ≤ t → a (l + j) = b (l + j) := by
  induction t with
  | zero =>
    obtain ⟨a, ha, ha0, _⟩ := hedge l
    refine ⟨SymbolicDynamics.FullShift.shift (-l) a, hshift a ha (-l), ?_⟩
    intro j hj0 hjt
    have hj : j = 0 := by omega
    subst j
    simpa only [SymbolicDynamics.FullShift.shift_apply, add_zero, neg_add_cancel]
      using ha0
  | succ t ih =>
    obtain ⟨a, ha, hagree⟩ := ih
    obtain ⟨d, hd, hd0, hd1⟩ := hedge (l + t)
    have hseam : a (l + t) = d 0 :=
      (hagree t (by omega) le_rfl).trans hd0.symm
    obtain ⟨c, hc, hpast, hfuture⟩ :=
      splice_at_integer L hshift hsplice a ha d hd (l + t) hseam
    refine ⟨c, hc, ?_⟩
    intro j hj0 hjt
    by_cases hj : j ≤ t
    · rw [hpast (l + j) (by omega)]
      exact hagree j hj0 hj
    · have hj : j = (t : ℤ) + 1 := by omega
      rw [hfuture (l + j) (by omega)]
      convert hd1 using 1 <;> congr 1 <;> omega

/-- Closedness upgrades finite-word realization to an entire bi-infinite path.
Source: Bowen, Global analysis I, Proposition (6.2), pp.36–37, closedness step;
Manning Lemma 6, p.428. Every product-open neighborhood specifies finitely many
coordinates. Enclose these in one finite integer interval and apply the preceding
finite-word induction; the resulting member of L is in that neighborhood. -/
theorem infinite_path_in_splice_set
    {S : Type*} [TopologicalSpace S] (L : Set (ℤ → S)) (hclosed : IsClosed L)
    (hshift : ∀ a ∈ L, ∀ k : ℤ, SymbolicDynamics.FullShift.shift k a ∈ L)
    (hsplice : ∀ a ∈ L, ∀ b ∈ L, a 0 = b 0 →
      ∃ c ∈ L, (∀ j : ℤ, j ≤ 0 → c j = a j) ∧
        (∀ j : ℤ, 0 ≤ j → c j = b j))
    (b : ℤ → S)
    (hedge : ∀ k : ℤ, ∃ a ∈ L, a 0 = b k ∧ a 1 = b (k + 1)) : b ∈ L := by
  classical
  rw [← hclosed.closure_eq]
  apply mem_closure_iff.mpr
  intro O hO hbO
  obtain ⟨I, U, hU, hUO⟩ := isOpen_pi_iff.mp hO b hbO
  let m : ℕ := I.sup Int.natAbs
  obtain ⟨a, ha, hagree⟩ :=
    finite_path_in_splice_set L hshift hsplice b hedge (-(m : ℤ)) (2 * m)
  refine ⟨a, hUO ?_, ha⟩
  intro j hj
  have hjm : j.natAbs ≤ m := Finset.le_sup (f := Int.natAbs) hj
  have hjlo : -(m : ℤ) ≤ j := by
    have hneg : -j ≤ (j.natAbs : ℤ) := by
      simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -j))
    have hcast : (j.natAbs : ℤ) ≤ m := by exact_mod_cast hjm
    omega
  have hjhi : j ≤ (m : ℤ) := by
    exact le_trans (Int.le_natAbs (a := j)) (by exact_mod_cast hjm)
  have heq := hagree (j + m) (by omega) (by omega)
  have heq' : a j = b j := by
    convert heq using 1 <;> congr 1 <;> omega
  exact heq' ▸ (hU j hj).2

/-- A nonempty closed finite-alphabet shift-invariant set closed under guarded
same-symbol splicing contains a periodic sequence. This supplies Manning Lemma 6's
p.428 finite-type-to-periodic step without assuming that arbitrary closed subshifts
have periodic points. Find a repeated symbol along one positive half-orbit, repeat
the intervening nonempty word by integer remainder, check every adjacent pair
(including the wraparound pair), and use the proved finite-word/closedness argument. -/
theorem periodic_sequence_in_splice_set
    {S : Type*} [Finite S] [TopologicalSpace S]
    (L : Set (ℤ → S)) (hne : L.Nonempty) (hclosed : IsClosed L)
    (hshift : ∀ a ∈ L, ∀ k : ℤ, SymbolicDynamics.FullShift.shift k a ∈ L)
    (hsplice : ∀ a ∈ L, ∀ b ∈ L, a 0 = b 0 →
      ∃ c ∈ L, (∀ j : ℤ, j ≤ 0 → c j = a j) ∧
        (∀ j : ℤ, 0 ≤ j → c j = b j)) :
    ∃ c ∈ L, ∃ p : ℕ, 0 < p ∧ ∀ j : ℤ, c (j + p) = c j := by
  classical
  obtain ⟨a, ha⟩ := hne
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun k : ℕ ↦ a (k : ℤ))
  have hrepeat : ∃ i j : ℕ, i < j ∧ a (i : ℤ) = a (j : ℤ) := by
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact ⟨i, j, hij, heq⟩
    · exact ⟨j, i, hji, heq.symm⟩
  obtain ⟨i, j, hij, heq⟩ := hrepeat
  let p : ℕ := j - i
  have hp : 0 < p := Nat.sub_pos_of_lt hij
  have hpZ : 0 < (p : ℤ) := by exact_mod_cast hp
  let b := SymbolicDynamics.FullShift.shift (i : ℤ) a
  have hb : b ∈ L := hshift a ha i
  have hbp : b (p : ℤ) = b 0 := by
    change a ((i : ℤ) + p) = a ((i : ℤ) + 0)
    have hip : (i : ℤ) + p = j := by
      dsimp [p]
      omega
    rw [hip, add_zero]
    exact heq.symm
  let c : ℤ → S := fun k ↦ b (k % p)
  have hc : c ∈ L := by
    apply infinite_path_in_splice_set L hclosed hshift hsplice c
    intro k
    let r : ℤ := k % p
    have hr0 : 0 ≤ r := Int.emod_nonneg k (ne_of_gt hpZ)
    have hrp : r < p := Int.emod_lt_of_pos k hpZ
    refine ⟨SymbolicDynamics.FullShift.shift r b, hshift b hb r, ?_, ?_⟩
    · simp only [SymbolicDynamics.FullShift.shift_apply, add_zero]
      rfl
    · change b (r + 1) = b ((k + 1) % p)
      have hmod : (k + 1) % (p : ℤ) = (r + 1) % p := by
        simp [r, Int.add_emod]
      rw [hmod]
      by_cases hlt : r + 1 < p
      · rw [Int.emod_eq_of_lt (by omega) hlt]
      · have hr : r + 1 = (p : ℤ) := by omega
        rw [hr]
        simpa using hbp
  refine ⟨c, hc, p, hp, ?_⟩
  intro k
  simp [c]

/-- The q-block version of the preceding closed-splice argument. Source: Manning
Lemma 6, pp.427–428, "we need only consider ... q=1", expanded literally by grouping
q consecutive symbols. No invariance under the one-symbol shift is assumed: only
translations by multiples of q are used. Grouping and ungrouping use Euclidean
integer division, so all negative coordinates and the entire zeroth block are kept. -/
theorem periodic_sequence_in_stride_splice_set
    {S : Type*} [Finite S] [TopologicalSpace S]
    (L : Set (ℤ → S)) (hne : L.Nonempty) (hclosed : IsClosed L)
    (q : ℕ) (hq : 0 < q)
    (hshift : ∀ a ∈ L, ∀ k : ℤ, SymbolicDynamics.FullShift.shift ((q : ℤ) * k) a ∈ L)
    (hsplice : ∀ a ∈ L, ∀ b ∈ L, a 0 = b 0 →
      ∃ c ∈ L, (∀ j : ℤ, j ≤ 0 → c j = a j) ∧
        (∀ j : ℤ, 0 ≤ j → c j = b j)) :
    ∃ c ∈ L, ∃ p : ℕ, 0 < p ∧ ∀ j : ℤ, c (j + q * p) = c j := by
  classical
  have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
  let group : (ℤ → S) → ℤ → Fin q → S := fun a k i ↦ a (q * k + i)
  let ungroup : (ℤ → Fin q → S) → ℤ → S := fun a j ↦
    a (j / q) ⟨(j % q).toNat, by
      have hh := Int.emod_lt_of_pos j hqZ
      have hh0 := Int.emod_nonneg j (ne_of_gt hqZ)
      omega⟩
  have hug : ∀ a, ungroup (group a) = a := by
    intro a
    funext j
    dsimp [ungroup, group]
    congr 1
    have hh0 := Int.emod_nonneg j (ne_of_gt hqZ)
    rw [Int.toNat_of_nonneg hh0]
    have he := Int.emod_add_mul_ediv j q
    omega
  have hgu : ∀ a, group (ungroup a) = a := by
    intro a
    funext k i
    dsimp [ungroup, group]
    have hi0 : 0 ≤ (i : ℤ) := by omega
    have hiq : (i : ℤ) < q := by exact_mod_cast i.isLt
    have hdiv : ((q : ℤ) * k + i) / q = k := by
      rw [Int.mul_add_ediv_left _ _ (ne_of_gt hqZ)]
      rw [Int.ediv_eq_zero_of_lt hi0 hiq]
      omega
    have hmod : ((q : ℤ) * k + i) % q = i := by
      rw [Int.mul_add_emod_self_left, Int.emod_eq_of_lt hi0 hiq]
    rw [hdiv]
    congr 1
    apply Fin.ext
    simp only [hmod, Int.toNat_natCast]
  have huc : Continuous ungroup := by
    apply continuous_pi
    intro j
    exact (continuous_apply _).comp (continuous_apply _)
  let Lb : Set (ℤ → Fin q → S) := ungroup ⁻¹' L
  have hLb : Lb.Nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨group a, by simpa only [Lb, mem_preimage, hug] using ha⟩
  have hLbc : IsClosed Lb := hclosed.preimage huc
  have hLbs : ∀ a ∈ Lb, ∀ k : ℤ,
      SymbolicDynamics.FullShift.shift k a ∈ Lb := by
    intro a ha k
    have heq : ungroup (SymbolicDynamics.FullShift.shift k a) =
        SymbolicDynamics.FullShift.shift ((q : ℤ) * k) (ungroup a) := by
      funext j
      dsimp [ungroup, SymbolicDynamics.FullShift.shift]
      have hdiv : ((q : ℤ) * k + j) / q = k + j / q := by
        rw [Int.mul_add_ediv_left _ _ (ne_of_gt hqZ)]
      have hmod : ((q : ℤ) * k + j) % q = j % q := by
        rw [Int.mul_add_emod_self_left]
      simp only [hdiv, hmod]
    change ungroup _ ∈ L
    rw [heq]
    exact hshift _ ha k
  have hLbsp : ∀ a ∈ Lb, ∀ b ∈ Lb, a 0 = b 0 →
      ∃ c ∈ Lb, (∀ j : ℤ, j ≤ 0 → c j = a j) ∧
        (∀ j : ℤ, 0 ≤ j → c j = b j) := by
    intro a ha b hb hab
    have heq0 : ungroup a 0 = ungroup b 0 := by
      dsimp [ungroup]
      simp only [Int.zero_ediv]
      rw [hab]
    obtain ⟨c, hc, hpast, hfuture⟩ := hsplice _ ha _ hb heq0
    refine ⟨group c, ?_, ?_, ?_⟩
    · change ungroup (group c) ∈ L
      simpa only [hug] using hc
    · intro k hk
      funext i
      change c ((q : ℤ) * k + i) = a k i
      by_cases hk0 : k = 0
      · subst k
        rw [hfuture _ (by omega)]
        have ht := congrFun (congrFun (hgu b) 0) i
        dsimp [group] at ht
        simpa only [mul_zero, zero_add, hab] using ht
      · have hiq : (i : ℤ) < q := by exact_mod_cast i.isLt
        have hkneg : k ≤ -1 := by omega
        rw [hpast _ (by nlinarith)]
        exact congrFun (congrFun (hgu a) k) i
    · intro k hk
      funext i
      change c ((q : ℤ) * k + i) = b k i
      rw [hfuture _ (by positivity)]
      exact congrFun (congrFun (hgu b) k) i
  obtain ⟨a, ha, p, hp, hperiod⟩ :=
    periodic_sequence_in_splice_set Lb hLb hLbc hLbs hLbsp
  refine ⟨ungroup a, ha, p, hp, ?_⟩
  intro j
  change a ((j + ((q * p : ℕ) : ℤ)) / q) _ = a (j / q) _
  have hdiv : (j + ((q * p : ℕ) : ℤ)) / q = j / q + p := by
    rw [Nat.cast_mul, mul_comm (q : ℤ) (p : ℤ),
      Int.add_mul_ediv_right _ _ (ne_of_gt hqZ)]
  have hmod : (j + ((q * p : ℕ) : ℤ)) % q = j % q := by
    rw [Nat.cast_mul, mul_comm (q : ℤ) (p : ℤ), Int.add_mul_emod_self_right]
  simp only [hdiv, hperiod]
  congr 1
  apply Fin.ext
  simpa only [Nat.cast_mul] using congrArg Int.toNat hmod


end HolomorphicAnosov
