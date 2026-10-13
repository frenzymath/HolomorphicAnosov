import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTime

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter

/-- Integer periodic time is unchanged by adding its positive period. This is the elementary remainder identity used in extending Manning's finite periodic words to all integer times. -/
theorem integerPeriodicTime_period {m : ℕ} (hm : 0 < m) (j : ℤ) :
    integerPeriodicTime hm (j + m) = integerPeriodicTime hm j := by
  apply Fin.ext
  simp [integerPeriodicTime]

end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
