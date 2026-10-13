import HolomorphicAnosov.Dynamics.HirschPughNativeLeafSystem
import HolomorphicAnosov.Dynamics.HirschPughHyperbolicSetFactOne
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathMap
import HolomorphicAnosov.Dynamics.NativeLeafPathAdvanceSpeed
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathSpeedIntegrable

namespace HolomorphicAnosov
open Set MeasureTheory
open scoped ContDiff Manifold
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local notation "I" => 𝓘(ℝ, E)

/-- The original native advance contracts every actual finite path's pullback
length by its tangent bound. This agent-written integral application follows
Lee (2003), p.275's finite-piece length formula: speeds are integrable on each
closed interval, the pointwise native speed estimate can be integrated, and
finite summation preserves the same factor. -/
theorem nativeLeafPath_advance_length_le
    (f : Diffeomorph I I M M ∞)
    {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (S : NativeInvariantLeafSystem I D f)
    (h : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (θ : ℝ)
    (hθ : ∀ (x : M) (v : TangentSpace I x), v ∈ D x →
      hyperbolicRiemannianNorm h (mfderiv I I f x v) ≤ θ * hyperbolicRiemannianNorm h v)
    (x : M) {y z : (S.leaf x).Carrier}
    (p : RiemannianPiecewiseSmoothPath 𝓘(ℝ, Fin (S.leaf x).rank → ℝ) y z) :
    nativeLeafPathLength I h (S.leaf (f x)) (p.map (S.advance x) (S.advance x).contMDiff) ≤
      θ * nativeLeafPathLength I h (S.leaf x) p := by
  let c := p.map (S.leaf x).inclusion (S.leaf x).inclusion_smooth
  let q := (p.map (S.advance x) (S.advance x).contMDiff).map
    (S.leaf (f x)).inclusion (S.leaf (f x)).inclusion_smooth
  change (∑ i : Fin (p.n + 1), ∫ t in p.time i.castSucc..p.time i.succ, q.speed h i t) ≤
    θ * ∑ i : Fin (p.n + 1), ∫ t in p.time i.castSucc..p.time i.succ, c.speed h i t
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← intervalIntegral.integral_const_mul]
  have hle := p.time_strictMono.monotone (Fin.castSucc_le_succ i)
  apply intervalIntegral.integral_mono_on hle
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr (q.speed_integrableOn h i)
  · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr
      (c.speed_integrableOn h i)).const_mul θ
  · intro t ht
    exact nativeLeafPath_advance_speed_le f S h θ hθ x p i ht

end HolomorphicAnosov
