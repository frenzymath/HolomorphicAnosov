import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace HolomorphicAnosov.Analysis.MarkedRectangle

/-- The real parameter for the symmetric four-prevertex normalization.
Source: the explicit algebraic normalization in Step 1 of
`analysis.marked_rectangle_g3_disk_schwarz_christoffel`, following Bak–Newman,
Complex Analysis, third edition, pp.184–186. If R>1, put s=√(1−1/R).
Then 0<s<1 and k=(1−s)/(1+s) lies in (0,1). Clearing the nonzero denominators
and using s²=1−1/R proves the cross-ratio identity. -/
theorem schwarzChristoffelModulus (R : ℝ) (hR : 1 < R) :
    let k := (1 - Real.sqrt (1 - 1 / R)) / (1 + Real.sqrt (1 - 1 / R))
    0 < k ∧ k < 1 ∧ (1 + k) ^ 2 / (4 * k) = R := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hRne : R ≠ 0 := ne_of_gt hRpos
  have hinv : 0 < 1 / R := div_pos zero_lt_one hRpos
  have hinvlt : 1 / R < 1 := (div_lt_one hRpos).mpr hR
  let s := Real.sqrt (1 - 1 / R)
  have hspos : 0 < s := Real.sqrt_pos.mpr (sub_pos.mpr hinvlt)
  have hsq : s ^ 2 = 1 - 1 / R := Real.sq_sqrt (sub_nonneg.mpr hinvlt.le)
  have hslt : s < 1 := by nlinarith
  have hden : 0 < 1 + s := by linarith
  have hnum : 0 < 1 - s := sub_pos.mpr hslt
  change 0 < (1 - s) / (1 + s) ∧ (1 - s) / (1 + s) < 1 ∧ _
  refine ⟨div_pos hnum hden, (div_lt_one hden).mpr (by linarith), ?_⟩
  have hrel : R * s ^ 2 = R - 1 := by
    rw [hsq]
    field_simp
  change (1 + (1 - s) / (1 + s)) ^ 2 / (4 * ((1 - s) / (1 + s))) = R
  field_simp [ne_of_gt hden, ne_of_gt hnum]
  nlinarith


end HolomorphicAnosov.Analysis.MarkedRectangle
