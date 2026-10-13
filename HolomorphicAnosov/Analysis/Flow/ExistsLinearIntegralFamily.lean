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

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace PicardVariationalWitnesses
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Actual operator-valued linear integral IVPs on ONE interval for every parameter.
The interval is chosen from the common coefficient bound, not from parameter continuity of
the solution. This is a direct application of Mathlib Picard--Lindelöf on the operator ball
of radius one about the identity, with zero initial-radius variation. Dimension zero is allowed. -/
theorem exists_linear_integral_family
    {P : Type*} (A : P → ℝ → E →L[ℝ] E) (S : ℝ) (hS : 0 < S) (K : ℝ≥0)
    (hAcont : ∀ p, ContinuousOn (A p) (Icc (-S) S))
    (hAbound : ∀ p, ∀ t ∈ Icc (-S) S, ‖A p t‖ ≤ K) :
    ∃ δ > 0, δ ≤ S ∧ ∃ Y : P → ℝ → E →L[ℝ] E, ∀ p,
      Continuous (Y p) ∧ ∀ t ∈ Icc (-δ) δ,
        Y p t = ContinuousLinearMap.id ℝ E + ∫ s in 0..t, (A p s).comp (Y p s) := by
  let I : E →L[ℝ] E := ContinuousLinearMap.id ℝ E
  let M : ℝ≥0 := K * (‖I‖₊ + 1)
  let δ : ℝ := min S (1 / ((M : ℝ) + 1))
  have hδ : 0 < δ := lt_min hS (by positivity)
  have hδS : δ ≤ S := min_le_left _ _
  have hsub : Icc (-δ) δ ⊆ Icc (-S) S := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have htime : (M : ℝ) * δ ≤ 1 := by
    calc
      (M : ℝ) * δ ≤ M * (1 / ((M : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left (min_le_right _ _) M.coe_nonneg
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity : (0 : ℝ) < M + 1)]
        linarith
  have hpicard (p : P) : IsPicardLindelof (fun t (V : E →L[ℝ] E) ↦ (A p t).comp V)
      (tmin := -δ) (tmax := δ) ⟨0, ⟨by linarith, hδ.le⟩⟩ I 1 0 M K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro V _ W _
      rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
      exact ((A p t).opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_right (hAbound p t (hsub ht)) (norm_nonneg _))
    · intro V _
      exact ((hAcont p).mono hsub).clm_comp continuousOn_const
    · intro t ht V hV
      have hnormV : ‖V‖ ≤ ‖I‖ + 1 := by
        have hh : ‖V - I‖ ≤ 1 := mem_closedBall_iff_norm.mp hV
        linarith [norm_le_norm_sub_add V I]
      exact ((A p t).opNorm_comp_le _).trans
        (by simpa only [M, NNReal.coe_mul, NNReal.coe_add, coe_nnnorm, NNReal.coe_one] using
          mul_le_mul (hAbound p t (hsub ht)) hnormV (norm_nonneg _) K.coe_nonneg)
    · simpa only [sub_zero, zero_sub, neg_neg, max_self, NNReal.coe_one,
        NNReal.coe_zero] using htime
  have hex (p : P) := exists_picard_family_with_range (hpicard p)
  choose β hβ using hex
  refine ⟨δ, hδ, hδS, (fun p ↦ β p I), ?_⟩
  intro p
  have hp := (hβ p).2 I (mem_closedBall_self (le_refl 0))
  exact ⟨hp.1, hp.2.2⟩

end PicardVariationalWitnesses
