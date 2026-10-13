import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTime

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter

/-- Integer periodic time sends addition of one to finite cyclic successor. This is the elementary remainder identity used in extending Manning's finite periodic words to all integer times. -/
theorem integerPeriodicTime_succ {m : ℕ} (hm : 0 < m) (j : ℤ) :
    integerPeriodicTime hm (j + 1) = nextTime hm (integerPeriodicTime hm j) := by
  apply Fin.ext
  simp only [integerPeriodicTime, nextTime]
  have hnon := Int.emod_nonneg j (show (m : ℤ) ≠ 0 by omega)
  have heq : (j + 1) % (m : ℤ) = (j % (m : ℤ) + 1) % (m : ℤ) := by
    simp only [Int.add_emod, Int.emod_emod]
  rw [heq, Int.toNat_emod (by omega) (by omega), Int.toNat_add hnon (by omega)]
  simp

end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
