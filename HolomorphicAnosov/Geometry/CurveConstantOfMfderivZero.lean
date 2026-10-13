import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.MeanValue

/-!
Smooth real curves with vanishing tangent derivative are constant. (Zhang, p.13)
-/

open scoped ContDiff

universe u v

namespace HolomorphicAnosov

attribute [local instance] complex_isManifold_real

/-- A smooth curve from `ℝ` to a manifold with zero tangent derivative is constant. (Lee, Prop.
6.10, p.134; Zhang, p.13) -/
theorem curve_constant_of_mfderiv_zero
    {d : ℕ} {M : Type v} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M] (c : ℝ → M)
    (hc : ContMDiff (modelWithCornersSelf ℝ ℝ) (realModel d) ∞ c)
    (hder : ∀ t, mfderiv (modelWithCornersSelf ℝ ℝ) (realModel d) c t = 0) :
    ∀ s t, c s = c t := by
  have hlocal : IsLocallyConstant c := by
    apply (IsLocallyConstant.iff_exists_open c).mpr
    intro t
    let e := extChartAt (realModel d) (c t)
    have hopen : IsOpen (c ⁻¹' (chartAt (ComplexModel d) (c t)).source) :=
      (chartAt (ComplexModel d) (c t)).open_source.preimage hc.continuous
    have ht : t ∈ c ⁻¹' (chartAt (ComplexModel d) (c t)).source := mem_chart_source _ _
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen t ht
    have hsmooth : ∀ s ∈ Metric.ball t ε,
        ContMDiffAt (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ (ComplexModel d)) ∞ (e ∘ c) s := by
      intro s hs
      exact (contMDiffAt_extChartAt' (hball hs)).comp s (hc s)
    have hdiff : DifferentiableOn ℝ (e ∘ c) (Metric.ball t ε) := by
      intro s hs
      exact (mdifferentiableAt_iff_differentiableAt.mp
        ((hsmooth s hs).mdifferentiableAt (by simp))).differentiableWithinAt
    have hzero : Set.EqOn (fderiv ℝ (e ∘ c)) 0 (Metric.ball t ε) := by
      intro s hs
      have hchart := (contMDiffAt_extChartAt' (hball hs)
        (I := realModel d) (n := ∞)).mdifferentiableAt (by simp)
      have hchain := mfderiv_comp s hchart ((hc s).mdifferentiableAt (by simp))
      rw [hder s, ContinuousLinearMap.comp_zero, mfderiv_eq_fderiv] at hchain
      exact hchain
    refine ⟨Metric.ball t ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_⟩
    intro s hs
    have heq := Metric.isOpen_ball.is_const_of_fderiv_eq_zero
      (convex_ball t ε).isPreconnected hdiff hzero hs (Metric.mem_ball_self hε)
    exact (chartAt (ComplexModel d) (c t)).injOn (hball hs) ht heq
  exact hlocal.apply_eq_of_preconnectedSpace


end HolomorphicAnosov
