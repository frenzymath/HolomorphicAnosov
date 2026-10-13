import HolomorphicAnosov.Analysis.SeparatelyHolomorphicSmooth
import HolomorphicAnosov.Geometry.ComplexModel




/-! This file identifies complex smooth coordinate maps with holomorphic maps on open subsets of finite-dimensional complex models. (Demailly, I §3.B–C).
-/
open scoped ContDiff

namespace HolomorphicAnosov

/-- On an open subset of a finite-dimensional complex model, complex smoothness is equivalent to complex differentiability. (Demailly, I §3.B–C). -/
theorem complex_contDiffOn_iff_differentiableOn {d e : ℕ}
    {s : Set (ComplexModel d)} (hs : IsOpen s) {f : ComplexModel d → ComplexModel e} :
    ContDiffOn ℂ ∞ f s ↔ DifferentiableOn ℂ f s := by
  constructor
  · intro hf
    exact hf.differentiableOn (by simp)
  · intro hf
    apply contDiffOn_of_continuousOn_separately_holomorphic hs hf.continuousOn
    intro z j
    exact hf.comp
      ((contDiff_update (𝕜 := ℂ) 1 z j).differentiable (by simp)).differentiableOn
      (fun _ ht ↦ ht)


end HolomorphicAnosov
