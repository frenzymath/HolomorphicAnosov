import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding

namespace HolomorphicAnosov

/-- The Bowen code shift translates every coordinate by the natural iterate.
Source: Bowen 1970, p.741; the proof is pure reindexing and retains negative times. -/
theorem code_shift_iterate_coordinate
    {N : ℕ} (B : Fin N → Fin N → Prop) (a : BowenBasicSetCoding.CodeSpace B)
    (r : ℕ) (j : ℤ) :
    ((BowenBasicSetCoding.codeShift B)^[r] a).val j = a.val ((r : ℤ) + j) := by
  induction r generalizing a with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [BowenBasicSetCoding.codeShift, SymbolicDynamics.FullShift.shift_apply]
    exact congrArg a.val (by omega)

end HolomorphicAnosov
