import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import HolomorphicAnosov.Analysis.Flow.ExistsPicardFamilyWithRange
import HolomorphicAnosov.Analysis.Flow.ExistsLinearIntegralFamily

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace PicardVariationalWitnesses
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Actual nonlinear and first-variational integral witnesses near any point of an OPEN
finite-dimensional C¹ field domain. All images stay in a genuine compact convex buffer
contained in that domain. The initial radius, nonlinear time interval, and then the common
linear-IVP interval are chosen from derived compact bounds. No extra regularity or metric
hypothesis is imposed, and no parameter continuity of the linear witness is assumed.

The outputs are the exact hypotheses of
`FirstVariationalDefect.first_variation_of_joint_integral_witnesses`, with `S` below as its
open witness interval and any `0 < T < S` as its compact two-sided conclusion interval.
That frozen scratch theorem is applied by the owner once an actual import is available. -/
theorem exists_picard_variational_integral_witnesses [FiniteDimensional ℝ E]
    (F : E → E) (Ω : Set E) (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ 1 F Ω)
    (x₀ : E) (hx₀ : x₀ ∈ Ω) :
    ∃ a > 0, ∃ r > 0, r < a ∧ closedBall x₀ a ⊆ Ω ∧
      ∃ S > 0, ∃ α : E → ℝ → E, ∃ Y : E → ℝ → E →L[ℝ] E,
        ContinuousOn (fun p : E × ℝ ↦ α p.1 p.2) (ball x₀ r ×ˢ Ioo (-S) S) ∧
        (∀ z ∈ ball x₀ r, ∀ t ∈ Ioo (-S) S, α z t ∈ closedBall x₀ a) ∧
        (∀ z ∈ ball x₀ r, α z 0 = z) ∧
        (∀ z ∈ ball x₀ r, ∀ t ∈ Ioo (-S) S,
          α z t = z + ∫ s in 0..t, F (α z s)) ∧
        (∀ z ∈ ball x₀ r, Continuous (Y z)) ∧
        (∀ z ∈ ball x₀ r, ∀ t ∈ Ioo (-S) S,
          Y z t = ContinuousLinearMap.id ℝ E +
            ∫ s in 0..t, (fderiv ℝ F (α z s)).comp (Y z s)) := by
  classical
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx₀)
  let a : ℝ≥0 := ⟨R / 2, (half_pos hR).le⟩
  let r : ℝ≥0 := a / 2
  have ha : 0 < (a : ℝ) := half_pos hR
  have hr : 0 < (r : ℝ) := half_pos ha
  have hra : (r : ℝ) < a := half_lt_self ha
  let B := closedBall x₀ (a : ℝ)
  have hB : IsCompact B := isCompact_closedBall _ _
  have hBΩ : B ⊆ Ω := (closedBall_subset_ball (half_lt_self hR)).trans hRΩ
  have hdiff : ∀ q ∈ B, DifferentiableAt ℝ F q := fun q hq ↦
    ((hF q (hBΩ hq)).contDiffAt (hΩ.mem_nhds (hBΩ hq))).differentiableAt one_ne_zero
  have hDF : ContinuousOn (fderiv ℝ F) B :=
    (hF.continuousOn_fderiv_of_isOpen hΩ (by norm_num)).mono hBΩ
  have hFc : ContinuousOn F B := fun q hq ↦
    (hdiff q hq).continuousAt.continuousWithinAt
  obtain ⟨CF, hCF⟩ := hB.exists_bound_of_continuousOn hFc
  obtain ⟨CD, hCD⟩ := hB.exists_bound_of_continuousOn hDF
  let L : ℝ≥0 := ⟨max 0 CF, le_max_left _ _⟩
  let K : ℝ≥0 := ⟨max 0 CD, le_max_left _ _⟩
  have hL : ∀ q ∈ B, ‖F q‖ ≤ L := fun q hq ↦ (hCF q hq).trans (le_max_right _ _)
  have hK : ∀ q ∈ B, ‖fderiv ℝ F q‖ ≤ K := fun q hq ↦
    (hCD q hq).trans (le_max_right _ _)
  have hlip : LipschitzOnWith K F B :=
    (convex_closedBall x₀ (a : ℝ)).lipschitzOnWith_of_nnnorm_fderiv_le hdiff
      (fun q hq ↦ by exact_mod_cast hK q hq)
  let S₀ : ℝ := ((a : ℝ) - r) / (L + 1)
  have hS₀ : 0 < S₀ := div_pos (sub_pos.mpr hra) (by positivity)
  have htime : (L : ℝ) * S₀ ≤ a - r := by
    calc
      (L : ℝ) * S₀ = (L / (L + 1)) * ((a : ℝ) - r) := by dsimp [S₀]; ring
      _ ≤ 1 * ((a : ℝ) - r) := by
        apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hra.le)
        rw [div_le_one (by positivity : (0 : ℝ) < L + 1)]
        linarith
      _ = (a : ℝ) - r := one_mul _
  have hpicard : IsPicardLindelof (fun _ ↦ F) (tmin := -S₀) (tmax := S₀)
      ⟨0, ⟨by linarith, hS₀.le⟩⟩ x₀ a r L K :=
    IsPicardLindelof.of_time_independent hL hlip (by simpa using htime)
  obtain ⟨α, hαcont, hα⟩ := exists_picard_family_with_range hpicard
  let P := {z : E // z ∈ closedBall x₀ (r : ℝ)}
  let A : P → ℝ → E →L[ℝ] E := fun z t ↦ fderiv ℝ F (α z t)
  have hAcont : ∀ z, ContinuousOn (A z) (Icc (-S₀) S₀) := by
    intro z
    exact hDF.comp (hα z z.2).1.continuousOn (fun t _ ↦ (hα z z.2).2.1 t)
  have hAbound : ∀ z, ∀ t ∈ Icc (-S₀) S₀, ‖A z t‖ ≤ K :=
    fun z t _ ↦ hK _ ((hα z z.2).2.1 t)
  obtain ⟨S, hS, hSS₀, Y₀, hY₀⟩ := exists_linear_integral_family A S₀ hS₀ K hAcont hAbound
  let Y : E → ℝ → E →L[ℝ] E := fun z ↦
    if hz : z ∈ closedBall x₀ (r : ℝ) then Y₀ ⟨z, hz⟩ else 0
  have hsub : Ioo (-S) S ⊆ Icc (-S₀) S₀ := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hball : ball x₀ (r : ℝ) ⊆ closedBall x₀ (r : ℝ) := ball_subset_closedBall
  refine ⟨a, ha, r, hr, hra, hBΩ, S, hS, α, Y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hαcont.mono (prod_mono hball hsub)
  · intro z hz t _
    exact (hα z (hball hz)).2.1 t
  · intro z hz
    have hh := (hα z (hball hz)).2.2 0 ⟨by linarith, hS₀.le⟩
    simpa using hh
  · intro z hz t ht
    exact (hα z (hball hz)).2.2 t (hsub ht)
  · intro z hz
    simpa only [Y, dite_eq_left (hball hz)] using (hY₀ ⟨z, hball hz⟩).1
  · intro z hz t ht
    simpa only [Y, dite_eq_left (hball hz), A] using
      (hY₀ ⟨z, hball hz⟩).2 t ⟨ht.1.le, ht.2.le⟩

end PicardVariationalWitnesses
