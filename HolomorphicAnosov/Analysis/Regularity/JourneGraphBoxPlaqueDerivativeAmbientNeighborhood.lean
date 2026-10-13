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
import HolomorphicAnosov.Analysis.Regularity.JourneGraphBoxPlaqueDerivativeCommonRadius

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

/-- Source: J1. Transfer the common leaf radius to a genuine ambient
neighborhood through the original graph-box homeomorphism. All inverse-chart
parameters and receiving points remain inside the original graph-box domain. -/
theorem graphBox_plaque_derivative_ambient_neighborhood
    {d c N n : ℕ} {α : ℝ} {Ω : Set (Block N)}
    (b : GraphBox d c N n α Ω) (hn : 1 ≤ n)
    {a₀ : Block N} (ha₀ : a₀ ∈ b.image) {ε : ℝ} (hε : 0 < ε) :
    let z₀ := (b.chart.symm ⟨a₀, ha₀⟩).val
    ∃ V : Set (Block N), IsOpen V ∧ a₀ ∈ V ∧ V ⊆ b.image ∧
      ∃ r : ℝ, 0 < r ∧ ∀ a ∈ V, ∀ ha : a ∈ b.image,
        let z := (b.chart.symm ⟨a, ha⟩).val
        ∀ x ∈ Metric.ball z.1 r,
          (x, z.2) ∈ Metric.ball 0 b.leafRadius ×ˢ Metric.ball 0 b.transverseRadius ∧
          ‖fderiv ℝ (b.plaque z.2) x - fderiv ℝ (b.plaque z₀.2) z₀.1‖ < ε := by
  let z₀ := b.chart.symm ⟨a₀, ha₀⟩
  obtain ⟨r, hr, hbound⟩ := graphBox_plaque_derivative_common_radius b hn z₀.property hε
  let W : Set ↥(Metric.ball (0 : Block d) b.leafRadius ×ˢ
      Metric.ball (0 : Block c) b.transverseRadius) :=
    Subtype.val ⁻¹' Metric.ball z₀.val r
  have hW : IsOpen W := Metric.isOpen_ball.preimage continuous_subtype_val
  let V : Set (Block N) := Subtype.val '' (b.chart '' W)
  have hV : IsOpen V := b.image_open.isOpenMap_subtype_val _ (b.chart.isOpenMap _ hW)
  have hmem : a₀ ∈ V := by
    refine ⟨⟨a₀, ha₀⟩, ?_, rfl⟩
    exact ⟨z₀, Metric.mem_ball_self hr, b.chart.apply_symm_apply _⟩
  have hsub : V ⊆ b.image := by
    rintro a ⟨u, hu, rfl⟩
    exact u.property
  refine ⟨V, hV, hmem, hsub, r, hr, ?_⟩
  intro a ha haimage
  obtain ⟨u, ⟨z, hz, hzu⟩, hua⟩ := ha
  have hu : u = ⟨a, haimage⟩ := Subtype.ext hua
  have hzinv : z = b.chart.symm ⟨a, haimage⟩ := by
    apply b.chart.injective
    simpa only [b.chart.apply_symm_apply] using hzu.trans hu
  dsimp only
  intro x hx
  apply hbound (b.chart.symm ⟨a, haimage⟩).val _ x hx
  simpa only [W, Set.mem_preimage, hzinv] using hz

end HolomorphicAnosov.JourneLeafPolynomialApproximation
