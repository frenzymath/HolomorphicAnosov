import HolomorphicAnosov.Geometry.SmoothMetricMatrixInverseEntry
import Mathlib.Analysis.Calculus.ContDiff.Defs

open Module
open scoped ContDiff Matrix

namespace HolomorphicAnosov

noncomputable section

/-- The inverse-metric Koszul coefficient formula is smooth on its open coordinate domain (Andrews, Prop. 10.3.1). -/
theorem smooth_metric_koszul_coefficient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {s : Set E} (hs : IsOpen s)
    (G : E → Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ G z i j) s)
    (hdet : ∀ z ∈ s, (G z).det ≠ 0) (b : Basis (Fin n) ℝ E) (i j k : Fin n) :
    ContDiffOn ℝ ∞ (fun z ↦ (1 / 2 : ℝ) * ∑ l : Fin n,
      ((G z)⁻¹) k l * (fderiv ℝ (fun z ↦ G z j l) z (b i) +
        fderiv ℝ (fun z ↦ G z i l) z (b j) -
        fderiv ℝ (fun z ↦ G z i j) z (b l))) s := by
  have hd (r t : Fin n) (v : E) :
      ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ (fun z ↦ G z r t) z v) s :=
    ((hG r t).fderiv_of_isOpen hs (by simp)).clm_apply contDiffOn_const
  refine contDiffOn_const.mul (ContDiffOn.sum fun l _ ↦ ?_)
  exact (smooth_metric_matrix_inverse_entry G hG hdet k l).mul
    (((hd j l (b i)).add (hd i l (b j))).sub (hd i j (b l)))

end
end HolomorphicAnosov
