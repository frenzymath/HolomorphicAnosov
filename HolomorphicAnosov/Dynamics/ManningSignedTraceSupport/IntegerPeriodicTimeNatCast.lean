import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTime

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter

/-- Integer periodic time restricts to the given finite time. This is the elementary remainder identity used in extending Manning's finite periodic words to all integer times. -/
theorem integerPeriodicTime_natCast {m : ℕ} (hm : 0 < m) (t : Fin m) :
    integerPeriodicTime hm (t.val : ℤ) = t := by
  apply Fin.ext
  simp only [integerPeriodicTime, ← Int.natCast_emod, Int.toNat_natCast,
    Nat.mod_eq_of_lt t.isLt]

end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
