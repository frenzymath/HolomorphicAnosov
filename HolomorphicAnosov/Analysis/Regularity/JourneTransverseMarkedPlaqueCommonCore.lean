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
import HolomorphicAnosov.Analysis.Regularity.JourneGraphBoxPlaqueDerivativeAmbientNeighborhood
import HolomorphicAnosov.Analysis.Regularity.JourneTransversePlaqueCoprodBijective
import HolomorphicAnosov.Analysis.Regularity.JourneApproximatesLinearImageCore
import HolomorphicAnosov.Analysis.Regularity.JournePlaqueSumApproximates
import HolomorphicAnosov.Analysis.Regularity.JourneGraphBoxApproximatesOnBall

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

open scoped NNReal in
set_option backward.isDefEq.respectTransparency false in
/-- J1's common receiving ball for the original marked-plaque sums. (Glöckner, 2007) -/
theorem transverse_marked_plaque_common_core
    {p q n : ℕ} {α : ℝ} {Ω : Set (Block (p + q))}
    (hp : 1 ≤ p) (hn : 1 ≤ n)
    (F₁ : GraphFoliation p q (p + q) n α Ω)
    (F₂ : GraphFoliation q p (p + q) n α Ω)
    (ht : AreTransverse F₁ F₂) (i : F₁.Index) (j : F₂.Index)
    (a₀ : Block (p + q)) (h₁ : a₀ ∈ (F₁.box i).image)
    (h₂ : a₀ ∈ (F₂.box j).image) :
    ∃ W : Set (Block (p + q)), IsOpen W ∧ a₀ ∈ W ∧
      W ⊆ (F₁.box i).image ∩ (F₂.box j).image ∧
      ∃ r ρ : ℝ, ∃ K : ℝ≥0, 0 < r ∧ 0 < ρ ∧ 0 < K ∧ ∀ a ∈ W,
        ∀ (ha₁ : a ∈ (F₁.box i).image) (ha₂ : a ∈ (F₂.box j).image),
        let z₁ := ((F₁.box i).chart.symm ⟨a, ha₁⟩).val
        let z₂ := ((F₂.box j).chart.symm ⟨a, ha₂⟩).val
        let Ψ := fun z : Block p × Block q ↦
          (F₁.box i).plaque z₁.2 z.1 + (F₂.box j).plaque z₂.2 z.2 - a
        ∃ e : OpenPartialHomeomorph (Block p × Block q) (Block (p + q)),
          (e : _ → _) = Ψ ∧ e.source = Metric.ball (z₁.1, z₂.1) r ∧
          Ψ (z₁.1, z₂.1) = a ∧ Metric.ball a ρ ⊆ e.target ∧
          Metric.ball a ρ ⊆ Ω ∧
          (∀ u ∈ Metric.ball a ρ, ∀ v ∈ Metric.ball a ρ,
            ‖e.symm u - e.symm v‖ ≤ (K : ℝ) * ‖u - v‖) ∧
          ∀ z ∈ e.source,
            (z.1, z₁.2) ∈ Metric.ball 0 (F₁.box i).leafRadius ×ˢ
              Metric.ball 0 (F₁.box i).transverseRadius ∧
            (z.2, z₂.2) ∈ Metric.ball 0 (F₂.box j).leafRadius ×ˢ
              Metric.ball 0 (F₂.box j).transverseRadius := by
  let : NeZero p := ⟨by omega⟩
  let z₁₀ := ((F₁.box i).chart.symm ⟨a₀, h₁⟩).val
  let z₂₀ := ((F₂.box j).chart.symm ⟨a₀, h₂⟩).val
  let D₁ := fderiv ℝ ((F₁.box i).plaque z₁₀.2) z₁₀.1
  let D₂ := fderiv ℝ ((F₂.box j).plaque z₂₀.2) z₂₀.1
  let L := D₁.coprod D₂
  have hL : Function.Bijective L :=
    transverse_plaque_coprod_bijective F₁ F₂ hn ht i j a₀ h₁ h₂
  let A : (Block p × Block q) ≃L[ℝ] Block (p + q) :=
    (LinearEquiv.ofBijective L.toLinearMap hL).toContinuousLinearEquiv
  have hA : A.toContinuousLinearMap = L := ContinuousLinearMap.ext (fun _ ↦ rfl)
  let ε : ℝ≥0 := ‖A.symm.toContinuousLinearMap‖₊⁻¹ / 4
  have hε : 0 < ε := div_pos (inv_pos.mpr A.nnnorm_symm_pos) (by norm_num)
  have hsmall : ε + ε < ‖A.symm.toContinuousLinearMap‖₊⁻¹ := by
    rw [show ε + ε = ‖A.symm.toContinuousLinearMap‖₊⁻¹ / 2 by dsimp [ε]; ring]
    exact half_lt_self (inv_pos.mpr A.nnnorm_symm_pos)
  obtain ⟨V₁, hV₁, haV₁, hsub₁, r₁, hr₁, hbounds₁⟩ :=
    graphBox_plaque_derivative_ambient_neighborhood (F₁.box i) hn h₁
      (show (0 : ℝ) < ε by exact_mod_cast hε)
  obtain ⟨V₂, hV₂, haV₂, hsub₂, r₂, hr₂, hbounds₂⟩ :=
    graphBox_plaque_derivative_ambient_neighborhood (F₂.box j) hn h₂
      (show (0 : ℝ) < ε by exact_mod_cast hε)
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  let ρ₀ := ((‖A.symm.toContinuousLinearMap‖₊⁻¹ : ℝ) - (ε + ε : ℝ≥0)) * (r / 2)
  have hρ₀ : 0 < ρ₀ := mul_pos (sub_pos.mpr (by exact_mod_cast hsmall)) (half_pos hr)
  let K : ℝ≥0 := (‖A.symm.toContinuousLinearMap‖₊⁻¹ - (ε + ε))⁻¹
  have hK : 0 < K := inv_pos.mpr (tsub_pos_iff_lt.mpr hsmall)
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp ((F₁.box i).image_open.mem_nhds h₁)
  refine ⟨(V₁ ∩ V₂) ∩ Metric.ball a₀ (R / 2),
    (hV₁.inter hV₂).inter Metric.isOpen_ball, ⟨⟨haV₁, haV₂⟩,
      Metric.mem_ball_self (half_pos hR)⟩,
    (fun a ha ↦ ⟨hsub₁ ha.1.1, hsub₂ ha.1.2⟩),
    r, min ρ₀ (R / 2), K, hr, lt_min hρ₀ (half_pos hR), hK, ?_⟩
  intro a ha ha₁ ha₂
  let z₁ := ((F₁.box i).chart.symm ⟨a, ha₁⟩).val
  let z₂ := ((F₂.box j).chart.symm ⟨a, ha₂⟩).val
  let Ψ := fun z : Block p × Block q ↦
    (F₁.box i).plaque z₁.2 z.1 + (F₂.box j).plaque z₂.2 z.2 - a
  have hb₁ := hbounds₁ a ha.1.1 ha₁
  have hb₂ := hbounds₂ a ha.1.2 ha₂
  have hb₁' : ∀ x ∈ Metric.ball z₁.1 r,
      (x, z₁.2) ∈ Metric.ball 0 (F₁.box i).leafRadius ×ˢ
        Metric.ball 0 (F₁.box i).transverseRadius ∧
      ‖fderiv ℝ ((F₁.box i).plaque z₁.2) x - D₁‖ < ε :=
    fun x hx ↦ hb₁ x (Metric.ball_subset_ball (min_le_left _ _) hx)
  have hb₂' : ∀ x ∈ Metric.ball z₂.1 r,
      (x, z₂.2) ∈ Metric.ball 0 (F₂.box j).leafRadius ×ˢ
        Metric.ball 0 (F₂.box j).transverseRadius ∧
      ‖fderiv ℝ ((F₂.box j).plaque z₂.2) x - D₂‖ < ε :=
    fun x hx ↦ hb₂ x (Metric.ball_subset_ball (min_le_right _ _) hx)
  have happ : ApproximatesLinearOn Ψ A.toContinuousLinearMap
      (Metric.ball (z₁.1, z₂.1) r) (ε + ε) := by
    rw [hA]
    exact plaque_sum_approximates
      (graphBox_approximates_on_ball (F₁.box i) hn z₁.2 z₁.1 r D₁ ε
        (fun x hx ↦ (hb₁' x hx).1) (fun x hx ↦ (hb₁' x hx).2))
      (graphBox_approximates_on_ball (F₂.box j) hn z₂.2 z₂.1 r D₂ ε
        (fun x hx ↦ (hb₂' x hx).1) (fun x hx ↦ (hb₂' x hx).2)) a
  have hcenter : Ψ (z₁.1, z₂.1) = a := by
    have hP := (F₁.box i).chart_formula ((F₁.box i).chart.symm ⟨a, ha₁⟩)
    have hQ := (F₂.box j).chart_formula ((F₂.box j).chart.symm ⟨a, ha₂⟩)
    simp only [Homeomorph.apply_symm_apply] at hP hQ
    change a = (F₁.box i).plaque z₁.2 z₁.1 at hP
    change a = (F₂.box j).plaque z₂.2 z₂.1 at hQ
    simp only [Ψ, ← hP, ← hQ, add_sub_cancel_right]
  obtain ⟨e, he, hs, hcore⟩ :=
    approximates_linear_image_core Ψ (z₁.1, z₂.1) A r hr (ε + ε) (Or.inr hsmall) happ
  have htarget : Metric.ball a (min ρ₀ (R / 2)) ⊆ e.target := by
    rw [hcenter] at hcore
    exact (Metric.ball_subset_ball (min_le_left _ _)).trans hcore
  refine ⟨e, he, hs, hcenter, htarget, ?_, ?_, ?_⟩
  · intro w hw
    apply (F₁.box i).image_subset (hRsub ?_)
    have hw' : dist w a < R / 2 := hw.trans_le (min_le_right _ _)
    have ha' : dist a a₀ < R / 2 := ha.2
    exact (dist_triangle w a a₀).trans_lt (by linarith)
  · intro u hu v hv
    have hu' : e.symm u ∈ Metric.ball (z₁.1, z₂.1) r := hs ▸ e.map_target (htarget hu)
    have hv' : e.symm v ∈ Metric.ball (z₁.1, z₂.1) r := hs ▸ e.map_target (htarget hv)
    have hLip := (happ.antilipschitz (Or.inr hsmall)).le_mul_dist
      ⟨e.symm u, hu'⟩ ⟨e.symm v, hv'⟩
    change dist (e.symm u) (e.symm v) ≤ (K : ℝ) * dist (Ψ (e.symm u)) (Ψ (e.symm v)) at hLip
    rw [← he, e.right_inv (htarget hu), e.right_inv (htarget hv)] at hLip
    simpa only [dist_eq_norm] using hLip
  · intro z hz
    rw [hs] at hz
    simp only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hz
    exact ⟨(hb₁' z.1 hz.1).1, (hb₂' z.2 hz.2).1⟩

end HolomorphicAnosov.JourneLeafPolynomialApproximation
