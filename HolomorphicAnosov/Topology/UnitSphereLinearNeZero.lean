import Mathlib.Analysis.Normed.Module.Basic

namespace HolomorphicAnosov

open Set

/-- A linear equivalence sends a unit vector to a nonzero vector.
Source: the denominator guard in the norm-conversion step of
`topo.unit_sphere_simply_connected_g9`. Injectivity reduces a zero image to a zero
unit vector, contradicting its norm. -/
theorem unit_sphere_linear_ne_zero {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (v : {v : E // ‖v‖ = 1}) : e v.val ≠ 0 := by
  apply e.map_ne_zero_iff.mpr
  intro hv
  have := v.property
  simp [hv] at this

end HolomorphicAnosov

