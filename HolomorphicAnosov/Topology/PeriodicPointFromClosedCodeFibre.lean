import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding
import HolomorphicAnosov.Topology.SymbolicSplicePeriodic
import HolomorphicAnosov.Topology.CodeShiftIterateCoordinate

namespace HolomorphicAnosov

open Set

/-- Apply the finite-alphabet closed-splice argument to the ACTUAL Bowen CodeSpace,
then project its positive q*p period through the actual coding covariance.
Source: Manning Lemma 6, pp.427–428, Steps4–5; Bowen Proposition (6.2), pp.36–37.
The hypotheses here are precisely the closedness, stride invariance and guarded
splice conclusions to be proved for the target fibre in Steps2–3. No periodic
code, finite-type structure or point of the desired fibre is supplied. -/
theorem periodic_point_from_closed_code_fibre
    {N : ℕ} (B : Fin N → Fin N → Prop)
    {X : Type*} (F : X → X) (coding : BowenBasicSetCoding.CodeSpace B → X)
    (hcov : ∀ a, coding (BowenBasicSetCoding.codeShift B a) = F (coding a))
    (L : Set (BowenBasicSetCoding.CodeSpace B)) (hne : L.Nonempty)
    (hclosed : IsClosed L) (q : ℕ) (hq : 0 < q)
    (hshift : ∀ a ∈ L, ∀ k : ℤ, ∃ b ∈ L,
      ∀ j : ℤ, b.val j = a.val ((q : ℤ) * k + j))
    (hsplice : ∀ a ∈ L, ∀ b ∈ L, a.val 0 = b.val 0 →
      ∃ c ∈ L, (∀ j : ℤ, j ≤ 0 → c.val j = a.val j) ∧
        (∀ j : ℤ, 0 ≤ j → c.val j = b.val j)) :
    ∃ a ∈ L, ∃ r : ℕ, 1 ≤ r ∧ F^[r] (coding a) = coding a := by
  classical
  let Legal : Set (ℤ → Fin N) := {a | ∀ j : ℤ, B (a j) (a (j + 1))}
  have hLegal : IsClosed Legal := by
    have heq : Legal = ⋂ j : ℤ, {a : ℤ → Fin N | B (a j) (a (j + 1))} := by
      ext a
      simp [Legal]
    rw [heq]
    apply isClosed_iInter
    intro j
    have hc : Continuous (fun a : ℤ → Fin N ↦ (a j, a (j + 1))) :=
      (continuous_apply j).prodMk (continuous_apply (j + 1))
    exact (isClosed_discrete (s := {p : Fin N × Fin N | B p.1 p.2})).preimage hc
  let Lraw : Set (ℤ → Fin N) := Subtype.val '' L
  have hrawne : Lraw.Nonempty := hne.image _
  have hrawclosed : IsClosed Lraw := hLegal.isClosedMap_subtype_val L hclosed
  have hrawshift : ∀ a ∈ Lraw, ∀ k : ℤ,
      SymbolicDynamics.FullShift.shift ((q : ℤ) * k) a ∈ Lraw := by
    rintro a ⟨ac, hac, rfl⟩ k
    obtain ⟨b, hb, hbj⟩ := hshift ac hac k
    refine ⟨b, hb, ?_⟩
    funext j
    exact hbj j
  have hrawsplice : ∀ a ∈ Lraw, ∀ b ∈ Lraw, a 0 = b 0 →
      ∃ c ∈ Lraw, (∀ j : ℤ, j ≤ 0 → c j = a j) ∧
        (∀ j : ℤ, 0 ≤ j → c j = b j) := by
    rintro a ⟨ac, hac, rfl⟩ b ⟨bc, hbc, rfl⟩ hab
    obtain ⟨c, hc, hpast, hfuture⟩ := hsplice ac hac bc hbc hab
    exact ⟨c.val, ⟨c, hc, rfl⟩, hpast, hfuture⟩
  obtain ⟨a, ha, p, hp, hperiod⟩ :=
    periodic_sequence_in_stride_splice_set Lraw hrawne hrawclosed q hq
      hrawshift hrawsplice
  obtain ⟨ac, hac, rfl⟩ := ha
  have hcode : (BowenBasicSetCoding.codeShift B)^[q * p] ac = ac := by
    apply Subtype.ext
    funext j
    rw [code_shift_iterate_coordinate]
    simpa only [add_comm, Nat.cast_mul] using hperiod j
  have hiter : ∀ r : ℕ, ∀ a : BowenBasicSetCoding.CodeSpace B,
      coding ((BowenBasicSetCoding.codeShift B)^[r] a) = F^[r] (coding a) := by
    intro r
    induction r with
    | zero => intro a; rfl
    | succ r ih =>
      intro a
      rw [Function.iterate_succ_apply, ih, hcov, Function.iterate_succ_apply]
  refine ⟨ac, hac, q * p, by have := Nat.mul_pos hq hp; omega, ?_⟩
  rw [← hiter, hcode]


end HolomorphicAnosov
