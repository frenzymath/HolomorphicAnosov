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
import HolomorphicAnosov.Analysis.Regularity.JourneTransversePlaqueCoprodBijective

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

set_option backward.isDefEq.respectTransparency false in
/-- 188, the change of variables sending the two marked plaques onto coordinate axes; J1 applies the inverse function theorem to their sum. (Journé, 1988) -/
theorem transverse_marked_plaque_differential
    {p q n : ℕ} {α : ℝ} {Ω : Set (Block (p + q))}
    (F₁ : GraphFoliation p q (p + q) n α Ω)
    (F₂ : GraphFoliation q p (p + q) n α Ω)
    (hn : 1 ≤ n) (ht : AreTransverse F₁ F₂)
    (i : F₁.Index) (j : F₂.Index) (a : Block (p + q))
    (h₁ : a ∈ (F₁.box i).image) (h₂ : a ∈ (F₂.box j).image) :
    let z₁ := ((F₁.box i).chart.symm ⟨a, h₁⟩).val
    let z₂ := ((F₂.box j).chart.symm ⟨a, h₂⟩).val
    ∃ A : (Block p × Block q) ≃L[ℝ] Block (p + q),
      let Ψ := fun z : Block p × Block q ↦
        (F₁.box i).plaque z₁.2 z.1 + (F₂.box j).plaque z₂.2 z.2 - a
      Ψ (z₁.1, z₂.1) = a ∧ ContDiffAt ℝ n Ψ (z₁.1, z₂.1) ∧
        HasFDerivAt Ψ A.toContinuousLinearMap (z₁.1, z₂.1) := by
  dsimp only
  let z₁ := (F₁.box i).chart.symm ⟨a, h₁⟩
  let z₂ := (F₂.box j).chart.symm ⟨a, h₂⟩
  let P := (F₁.box i).plaque z₁.val.2
  let Q := (F₂.box j).plaque z₂.val.2
  let x := (z₁.val.1, z₂.val.1)
  let Ψ : Block p × Block q → Block (p + q) := fun z ↦ P z.1 + Q z.2 - a
  have hn' : (n : WithTop ℕ∞) ≠ 0 := by simpa using (show n ≠ 0 by omega)
  obtain ⟨K₁, _, hb₁⟩ := (F₁.box i).graph_bounds
  obtain ⟨K₂, _, hb₂⟩ := (F₂.box j).graph_bounds
  have hP : ContDiffAt ℝ n P z₁.val.1 := by
    have hg := ((hb₁ z₁.val.2 z₁.property.2).1).contDiffAt
      (Metric.isOpen_ball.mem_nhds z₁.property.1)
    exact contDiffAt_const.add ((F₁.box i).frame.contDiff.contDiffAt.comp z₁.val.1
      (contDiffAt_id.prodMk hg))
  have hQ : ContDiffAt ℝ n Q z₂.val.1 := by
    have hg := ((hb₂ z₂.val.2 z₂.property.2).1).contDiffAt
      (Metric.isOpen_ball.mem_nhds z₂.property.1)
    exact contDiffAt_const.add ((F₂.box j).frame.contDiff.contDiffAt.comp z₂.val.1
      (contDiffAt_id.prodMk hg))
  have hΨ : ContDiffAt ℝ n Ψ x :=
    ((hP.comp x contDiffAt_fst).add (hQ.comp x contDiffAt_snd)).sub contDiffAt_const
  let L := (fderiv ℝ P z₁.val.1).toLinearMap.coprod
    (fderiv ℝ Q z₂.val.1).toLinearMap
  have hL : Function.Bijective L :=
    transverse_plaque_coprod_bijective F₁ F₂ hn ht i j a h₁ h₂
  let A : (Block p × Block q) ≃L[ℝ] Block (p + q) :=
    (LinearEquiv.ofBijective L hL).toContinuousLinearEquiv
  have hD : HasFDerivAt Ψ A.toContinuousLinearMap x := by
    have hdP := hP.differentiableAt hn'
    have hdQ := hQ.differentiableAt hn'
    have hpcomp := hdP.hasFDerivAt.comp x
      (hasFDerivAt_fst (𝕜 := ℝ) (E := Block p) (F := Block q) (p := x))
    have hqcomp := hdQ.hasFDerivAt.comp x
      (hasFDerivAt_snd (𝕜 := ℝ) (E := Block p) (F := Block q) (p := x))
    convert! (hpcomp.add hqcomp).sub_const a using 1
  have hPx : P z₁.val.1 = a := by
    have hv := congrArg Subtype.val ((F₁.box i).chart.apply_symm_apply ⟨a, h₁⟩)
    exact ((F₁.box i).chart_formula z₁).symm.trans hv
  have hQx : Q z₂.val.1 = a := by
    have hv := congrArg Subtype.val ((F₂.box j).chart.apply_symm_apply ⟨a, h₂⟩)
    exact ((F₂.box j).chart_formula z₂).symm.trans hv
  have hcenter : Ψ x = a := by simp [Ψ, x, hPx, hQx]
  exact ⟨A, hcenter, hΨ, hD⟩

end HolomorphicAnosov.JourneLeafPolynomialApproximation
