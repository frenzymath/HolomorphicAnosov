import HolomorphicAnosov.Analysis.MarkedRectangleG3CaratheodorySameMap

/-!
# Positive four point marks on the source circle

Source: Lyubich, *Conformal Geometry*, §1.11, pp. 53--54.  The strict
single-period angle lift in `PositiveCircleFour` forces the four circle marks
to be distinct.  This small theorem is separated from the full Carathéodory
extension so rectangle consumers can reuse the edge-case check without
depending on its deferred extension theorem.
-/

noncomputable section

namespace HolomorphicAnosov.Analysis.MarkedRectangle

open Set

/-- A positive single-turn lift gives distinct underlying complex points.
The interval has length exactly `2π`, so native exponential injectivity applies.
Source: Lyubich §1.11, pp. 53--54. -/
theorem positiveCircleFour_ne_coe {u : Fin 4 → Circle}
    (hu : PositiveCircleFour u) (i j : Fin 4)
    (hij : (u i : ℂ) = (u j : ℂ)) : i = j := by
  obtain ⟨t, ht, hturn, heq⟩ := hu
  have hi : ∀ i : Fin 4, 2 * Real.pi * t i ∈ Icc (2 * Real.pi * t 0)
      (2 * Real.pi * t 3) := by
    intro i
    constructor
    · exact mul_le_mul_of_nonneg_left (ht.monotone (Fin.zero_le i)) (by positivity)
    · exact mul_le_mul_of_nonneg_left (ht.monotone (by omega)) (by positivity)
  have hexp : Circle.exp (2 * Real.pi * t i) = Circle.exp (2 * Real.pi * t j) := by
    apply Subtype.ext
    simpa [heq i, heq j, circlePhase] using hij
  have hijt := Circle.exp_injOn_Icc (by nlinarith [Real.pi_pos]) (hi i) (hi j) hexp
  exact ht.injective (mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) hijt)

end HolomorphicAnosov.Analysis.MarkedRectangle
