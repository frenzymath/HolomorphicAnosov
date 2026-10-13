import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.NextTime

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter

/-- Integer time reduced into the finite cycle of a positive-period tuple word.
The nonnegative Euclidean remainder also covers all negative times. -/
def integerPeriodicTime {m : ℕ} (hm : 0 < m) (j : ℤ) : Fin m :=
  ⟨(j % (m : ℤ)).toNat, by
    have := Int.emod_nonneg j (show (m : ℤ) ≠ 0 by omega)
    have := Int.emod_lt_of_pos j (show (0 : ℤ) < m by omega)
    omega⟩

end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
