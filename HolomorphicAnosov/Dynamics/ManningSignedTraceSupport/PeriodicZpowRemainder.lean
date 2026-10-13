import Mathlib.Dynamics.FixedPoints.Basic


namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped Classical
noncomputable section

/-- For a positive period, every integer orbit index is congruent to its finite cyclic remainder. -/
theorem periodic_zpow_remainder {X : Type*} (F : Equiv.Perm X) {m : ℕ} (hm : 0 < m)
    {x : X} (hx : ((F : X → X)^[m]) x = x) (j : ℤ) :
    (F ^ j) x = ((F : X → X)^[(j % (m : ℤ)).toNat]) x := by
  have hfix : Function.IsFixedPt ((F ^ (m : ℤ) : Equiv.Perm X) : X → X) x := by
    simpa only [Function.IsFixedPt, zpow_natCast, Equiv.Perm.coe_pow] using hx
  have hmult := (hfix.perm_zpow (j / (m : ℤ))).eq
  rw [← zpow_mul] at hmult
  calc
    (F ^ j) x = (F ^ (j % (m : ℤ) + (m : ℤ) * (j / (m : ℤ)))) x := by
      rw [Int.emod_add_mul_ediv]
    _ = (F ^ (j % (m : ℤ))) x := by
      rw [zpow_add, Equiv.Perm.mul_apply, hmult]
    _ = ((F : X → X)^[(j % (m : ℤ)).toNat]) x := by
      have hn : 0 ≤ j % (m : ℤ) := Int.emod_nonneg _ (by omega)
      nth_rw 1 [← Int.toNat_of_nonneg hn]
      rw [zpow_natCast, Equiv.Perm.coe_pow]


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
