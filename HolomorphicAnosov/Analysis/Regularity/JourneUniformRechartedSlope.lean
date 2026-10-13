import HolomorphicAnosov.Analysis.Regularity.JourneRechartedDerivative
import HolomorphicAnosov.Analysis.Regularity.JournePlaqueHigherHolder
import HolomorphicAnosov.Analysis.Regularity.JourneGraphBoxPlaqueDerivativeAmbientNeighborhood
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set
open scoped _root_.Topology

/-- Joint continuity of the original plaque derivatives and a uniform Hölder modulus for the inverse derivatives yield arbitrarily small recharted slopes on one common neighborhood and one common plaque radius. -/
theorem uniform_recharted_plaque_slope
    {d c N n : ℕ} {α : ℝ} {Ω : Set (Block N)}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : GraphBox d c N n α Ω) (hn : 1 ≤ n)
    {a₀ : Block N} (ha₀ : a₀ ∈ b.image)
    {A H β ρ σ : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H) (hβ : 0 < β)
    (hρ : 0 < ρ) (hσ : 0 < σ) :
    ∃ V : Set (Block N), IsOpen V ∧ a₀ ∈ V ∧ V ⊆ b.image ∧
      ∃ r : ℝ, 0 < r ∧ ∀ a ∈ V, ∀ ha : a ∈ b.image,
        ∀ y ∈ V, ∀ hy : y ∈ b.image,
        let za := (b.chart.symm ⟨a,ha⟩).val
        let zy := (b.chart.symm ⟨y,hy⟩).val
        ∀ u ∈ Metric.ball zy.1 r,
          (u,zy.2) ∈ Metric.ball 0 b.leafRadius ×ˢ Metric.ball 0 b.transverseRadius ∧
          b.plaque zy.2 u ∈ Metric.ball a ρ ∧
          ∀ (g : Block N → F) (I : Block d →L[ℝ] F),
            DifferentiableOn ℝ g (Metric.ball a ρ) →
            ‖fderiv ℝ g a‖ ≤ A →
            (∀ z ∈ Metric.ball a ρ,
              ‖fderiv ℝ g z-fderiv ℝ g a‖ ≤ H*‖z-a‖^β) →
            (fderiv ℝ g a).comp (fderiv ℝ (b.plaque za.2) za.1) = I →
            ‖fderiv ℝ (g ∘ b.plaque zy.2) u-I‖ ≤ σ := by
  obtain ⟨K,hK,hfull⟩ := graphBox_plaque_holder_bound b hn
  have hcont : ContinuousAt (fun t : ℝ ↦ H*t^β*K) 0 :=
    ((continuous_const.mul (Real.continuous_rpow_const hβ.le)).mul continuous_const).continuousAt
  have hev : ∀ᶠ t : ℝ in 𝓝 0, H*t^β*K < σ/2 :=
    hcont.eventually (gt_mem_nhds (by simpa [Real.zero_rpow hβ.ne'] using half_pos hσ))
  obtain ⟨v,hv,hvbound⟩ := Metric.eventually_nhds_iff.mp hev
  let ν := min (ρ/2) (v/2)
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hνρ : ν < ρ := (min_le_left _ _).trans_lt (half_lt_self hρ)
  have hνv : ν < v := (min_le_right _ _).trans_lt (half_lt_self hv)
  have hsmall : H*ν^β*K ≤ σ/2 :=
    (hvbound (show dist ν 0 < v by simpa [dist_zero_right,Real.norm_of_nonneg hν.le] using hνv)).le
  obtain ⟨V₀,hV₀,haV₀,hVsub,r₀,hr₀,hderiv⟩ :=
    graphBox_plaque_derivative_ambient_neighborhood b hn ha₀
      (show 0 < σ/(4*(A+1)) by positivity)
  let V := V₀ ∩ Metric.ball a₀ (ν/8)
  let r := min r₀ (ν/(4*(K+1)))
  have hr : 0 < r := by dsimp [r]; positivity
  have hr₀le : r ≤ r₀ := min_le_left _ _
  have hKr : K*r ≤ ν/4 := by
    have ht := (le_div_iff₀ (show 0 < 4*(K+1) by positivity)).mp (min_le_right r₀ (ν/(4*(K+1))))
    change r*(4*(K+1)) ≤ ν at ht
    nlinarith
  refine ⟨V,hV₀.inter Metric.isOpen_ball,⟨haV₀,Metric.mem_ball_self (by positivity)⟩,
    fun z hz ↦ hVsub hz.1,r,hr,?_⟩
  intro a ha hai y hy hyi
  dsimp only
  let za := (b.chart.symm ⟨a,hai⟩).val
  let zy := (b.chart.symm ⟨y,hyi⟩).val
  intro u hu
  have hu₀ : u ∈ Metric.ball zy.1 r₀ := Metric.ball_subset_ball hr₀le hu
  obtain ⟨hdom,hclosey⟩ := hderiv y hy.1 hyi u hu₀
  have hclosea := (hderiv a ha.1 hai za.1 (Metric.mem_ball_self hr₀)).2
  have hpair : ‖fderiv ℝ (b.plaque zy.2) u-fderiv ℝ (b.plaque za.2) za.1‖ ≤
      σ/(2*(A+1)) := by
    have htri := dist_triangle (fderiv ℝ (b.plaque zy.2) u)
      (fderiv ℝ (b.plaque (b.chart.symm ⟨a₀,ha₀⟩).val.2) (b.chart.symm ⟨a₀,ha₀⟩).val.1)
      (fderiv ℝ (b.plaque za.2) za.1)
    simp only [dist_eq_norm] at htri
    rw [norm_sub_rev (fderiv ℝ (b.plaque (b.chart.symm ⟨a₀,ha₀⟩).val.2)
      (b.chart.symm ⟨a₀,ha₀⟩).val.1)] at htri
    have heq : σ/(2*(A+1)) = 2*(σ/(4*(A+1))) := by field_simp; ring
    rw [heq]
    linarith
  have hfy := hfull zy.2 (b.chart.symm ⟨y,hyi⟩).property.2
  have hfd : DifferentiableOn ℝ (b.plaque zy.2) (Metric.ball 0 b.leafRadius) :=
    hfy.1.differentiableOn (by simp; omega)
  have hfnorm : ∀ z ∈ Metric.ball (0:Block d) b.leafRadius,
      ‖fderiv ℝ (b.plaque zy.2) z‖ ≤ K := by
    intro z hz
    simpa only [norm_iteratedFDeriv_one] using hfy.2.1 1 hn z hz
  have hanchor : b.plaque zy.2 zy.1 = y := by
    have he := b.chart_formula (b.chart.symm ⟨y,hyi⟩)
    simpa [GraphBox.plaque,zy] using he.symm
  have hmove := (convex_ball (0:Block d) b.leafRadius).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz ↦ (hfd z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)) hfnorm
    (b.chart.symm ⟨y,hyi⟩).property.1 hdom.1
  rw [hanchor] at hmove
  have huy : ‖b.plaque zy.2 u-y‖ ≤ ν/4 :=
    (hmove.trans (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hu).le hK)).trans hKr
  have hya : ‖y-a‖ < ν/4 := by
    have H := dist_triangle y a₀ a
    rw [dist_comm a₀ a] at H
    have hyν := Metric.mem_ball.mp hy.2
    have haν := Metric.mem_ball.mp ha.2
    rw [← dist_eq_norm]
    linarith
  have hua : ‖b.plaque zy.2 u-a‖ < ν := by
    have H := dist_triangle (b.plaque zy.2 u) y a
    simp only [dist_eq_norm] at H
    linarith
  have huρ : b.plaque zy.2 u ∈ Metric.ball a ρ := by
    rw [Metric.mem_ball,dist_eq_norm]
    exact hua.trans hνρ
  refine ⟨hdom,huρ,?_⟩
  intro g I hg hgA hgH hgI
  have hginv : ‖fderiv ℝ g (b.plaque zy.2 u)-fderiv ℝ g a‖ ≤ H*ν^β :=
    (hgH _ huρ).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hua.le hβ.le) hH)
  have hb := recharted_plaque_derivative_close g (b.plaque zy.2) a u
    (fderiv ℝ (b.plaque za.2) za.1) I A K (H*ν^β) (σ/(2*(A+1)))
    (by positivity) hA ((hg _ huρ).differentiableAt (Metric.isOpen_ball.mem_nhds huρ))
    ((hfd u hdom.1).differentiableAt (Metric.isOpen_ball.mem_nhds hdom.1))
    hgI hgA (hfnorm u hdom.1) hginv hpair
  apply hb.trans
  have hAσ : A*(σ/(2*(A+1))) ≤ σ/2 := by
    have he : (σ/(2*(A+1)))*(2*(A+1)) = σ := div_mul_cancel₀ _ (by positivity)
    have hnon : 0 ≤ σ/(2*(A+1)) := by positivity
    nlinarith
  linarith

end HolomorphicAnosov.JourneLeafPolynomialApproximation
