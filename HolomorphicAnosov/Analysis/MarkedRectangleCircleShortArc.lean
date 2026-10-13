import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Linarith

namespace HolomorphicAnosov.Analysis.MarkedRectangle
open Set
/-- Short angular intervals with identical ordered endpoints have identical circle images. -/
lemma exp_short_image_eq {a b c d : ℝ}
    (hab : a < b) (hba : b < a + 2 * Real.pi)
    (hcd : c < d) (hdc : d < c + 2 * Real.pi)
    (hac : Circle.exp a = Circle.exp c) (hbd : Circle.exp b = Circle.exp d) :
    Circle.exp '' Icc a b = Circle.exp '' Icc c d := by
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hac
  have hshift (t : ℝ) : Circle.exp (t - k * (2 * Real.pi)) = Circle.exp t := by
    simpa only [zsmul_eq_mul] using Circle.periodic_exp.sub_zsmul_eq (x := t) k
  have he : b - k * (2 * Real.pi) = d := by
    apply Circle.exp_injOn_Ico (a := c) (b := c + 2 * Real.pi) (by linarith)
    · constructor <;> linarith
    · constructor <;> linarith
    · rw [hshift, hbd]
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t - k * (2 * Real.pi), ⟨by linarith [ht.1], by linarith [ht.2]⟩,
      hshift t⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t + k * (2 * Real.pi), ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    simpa only [add_sub_cancel_right] using (hshift (t + k * (2 * Real.pi))).symm


end HolomorphicAnosov.Analysis.MarkedRectangle
