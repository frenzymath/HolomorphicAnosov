import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Continuity of a segment Cauchy integral in its pole

DAG node: `analysis.polygon_segment_kernel_continuous_g17`.
Source: Conway, Functions of One Complex Variable, second edition (1978),
VIII Proposition 1.1, pp.195–196, extension of the surviving contour formula
across the grid. The parameter-integral implementation below is agent-written.
-/

namespace HolomorphicAnosov.Analysis.Complex
open Set

/-- A segment contained in `U \ L` has a Cauchy integral continuous in its pole
on `L`, for every function continuous on `U`. No compactness or closedness of
`L` is needed; the segment parameter interval itself is compact.

Proof: clamp the real parameter to `[0,1]`. The clamped segment is continuous,
its image lies in `U`, and its image avoids every pole in `L`. Therefore the
kernel is jointly continuous on `L × ℝ`, using the subtype topology on `L`.
The fixed-endpoint parameterized interval-integral theorem gives a continuous
integral on `L`. On `[0,1]` the clamp is the identity, so this is the original
segment integral. Multiplication by the constant tangent preserves continuity.
For coincident endpoints the integral is zero, and empty `L` is vacuous.
This expands the contour-continuity step of Conway VIII.1.1, pp.195–196. -/
theorem polygon_segment_kernel_continuousOn (L U : Set ℂ)
    (f : ℂ → ℂ) (hf : ContinuousOn f U) (a b : ℂ)
    (he : ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap a b t ∈ U \ L) :
    ContinuousOn (fun z ↦ ((b - a) * ∫ t in (0 : ℝ)..1,
      f (AffineMap.lineMap a b t) / (AffineMap.lineMap a b t - z))) L := by
  let α (t : ℝ) := AffineMap.lineMap a b (max 0 (min 1 t))
  have hα : Continuous α := by unfold α; fun_prop
  have hαmem (t : ℝ) : α t ∈ U \ L := by
    apply he
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hc : Continuous (fun p : L × ℝ ↦ f (α p.2) / (α p.2 - (p.1 : ℂ))) := by
    apply Continuous.div
    · exact hf.comp_continuous (hα.comp continuous_snd) (fun p ↦ (hαmem p.2).1)
    · fun_prop
    · intro p h
      exact (hαmem p.2).2 (sub_eq_zero.mp h ▸ p.1.property)
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume) (f := fun (z : L) (t : ℝ) ↦ f (α t) / (α t - z)) hc 0 1
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (fun z : L ↦ ((b - a) * ∫ t in (0 : ℝ)..1,
      f (AffineMap.lineMap a b t) / (AffineMap.lineMap a b t - z))) =
      (fun z : L ↦ (b - a) * ∫ t in (0 : ℝ)..1, f (α t) / (α t - z)) := by
    funext z
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    simp [α, max_eq_right ht'.1, min_eq_right ht'.2]
  change Continuous (fun z : L ↦ ((b - a) * ∫ t in (0 : ℝ)..1,
      f (AffineMap.lineMap a b t) / (AffineMap.lineMap a b t - z)))
  rw [heq]
  exact continuous_const.mul hi

end HolomorphicAnosov.Analysis.Complex
