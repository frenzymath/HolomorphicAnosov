import HolomorphicAnosov.Analysis.BilinearHolderBound
import HolomorphicAnosov.Analysis.CompositionHolderBound
import HolomorphicAnosov.Analysis.Regularity.PolynomialBallDerivativeEstimate
import HolomorphicAnosov.Analysis.Regularity.PolynomialMeasurableSubsetDerivativeEstimate
import HolomorphicAnosov.Analysis.WellsLipschitzPerturbationSmoothInverse
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import HolomorphicAnosov.Analysis.Regularity.GraphFoliationData
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Prod
import HolomorphicAnosov.Analysis.Regularity.JourneGraphBoxPlaqueFderivInjective

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

/-- 187–188 and J1. (Journé, 1988) -/
theorem transverse_plaque_coprod_bijective
    {p q n : ℕ} {α : ℝ} {Ω : Set (Block (p + q))}
    (F₁ : GraphFoliation p q (p + q) n α Ω)
    (F₂ : GraphFoliation q p (p + q) n α Ω)
    (hn : 1 ≤ n) (ht : AreTransverse F₁ F₂)
    (i : F₁.Index) (j : F₂.Index) (a : Block (p + q))
    (h₁ : a ∈ (F₁.box i).image) (h₂ : a ∈ (F₂.box j).image) :
    let z₁ := ((F₁.box i).chart.symm ⟨a, h₁⟩).val
    let z₂ := ((F₂.box j).chart.symm ⟨a, h₂⟩).val
    Function.Bijective
      ((fderiv ℝ ((F₁.box i).plaque z₁.2) z₁.1).toLinearMap.coprod
        (fderiv ℝ ((F₂.box j).plaque z₂.2) z₂.1).toLinearMap) := by
  dsimp only
  let z₁ := (F₁.box i).chart.symm ⟨a, h₁⟩
  let z₂ := (F₂.box j).chart.symm ⟨a, h₂⟩
  have hi := graphBox_plaque_fderiv_injective (F₁.box i) hn z₁.property.2 z₁.property.1
  have hj := graphBox_plaque_fderiv_injective (F₂.box j) hn z₂.property.2 z₂.property.1
  have hc := ht i j a h₁ h₂
  change IsCompl (LinearMap.range (fderiv ℝ ((F₁.box i).plaque z₁.val.2) z₁.val.1).toLinearMap)
    (LinearMap.range (fderiv ℝ ((F₂.box j).plaque z₂.val.2) z₂.val.1).toLinearMap) at hc
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_coprod_of_disjoint_range _ _ hc.disjoint,
      LinearMap.ker_eq_bot.mpr hi, LinearMap.ker_eq_bot.mpr hj]
    simp
  · apply LinearMap.range_eq_top.mp
    rw [LinearMap.range_coprod]
    exact hc.sup_eq_top

end HolomorphicAnosov.JourneLeafPolynomialApproximation
