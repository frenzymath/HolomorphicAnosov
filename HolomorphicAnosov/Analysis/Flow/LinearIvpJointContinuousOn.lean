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
import HolomorphicAnosov.Analysis.Flow.LinearIvpUniformNearInitial

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace FirstVariationalDefect
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Joint continuity of the actual variational IVP on the initial-set/closed-time rectangle.
Uniform coefficient continuity and the preceding operator-norm comparison supply the initial
parameter continuity, while the actual ODE supplies time continuity. -/
theorem linear_ivp_joint_continuousOn
    (A : E × ℝ → E →L[ℝ] E) (Y : E → ℝ → E →L[ℝ] E)
    (U : Set E) (I : Set ℝ) (hU : IsOpen U) (hI : IsOpen I)
    (hAcont : ContinuousOn A (U ×ˢ I))
    (T : ℝ) (hT : 0 ≤ T) (hseg : Icc 0 T ⊆ I) (K : ℝ≥0)
    (hA : ∀ z ∈ U, ∀ t ∈ Icc 0 T, ‖A (z, t)‖ ≤ K)
    (hY : ∀ z ∈ U, ∀ t ∈ Icc 0 T,
      HasDerivAt (Y z) ((A (z, t)).comp (Y z t)) t)
    (L : E →L[ℝ] E) (hinit : ∀ z ∈ U, Y z 0 = L) :
    ContinuousOn (fun p : E × ℝ ↦ Y p.1 p.2) (U ×ˢ Icc 0 T) := by
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨r, hr, hparam⟩ := linear_ivp_uniform_near_initial A Y U I hU hI hAcont
    T hT hseg K hA hY L hinit x hx (ε / 2) (half_pos hε)
  obtain ⟨s, hs, htime⟩ := Metric.continuousAt_iff.mp
    (hY x hx t ht).continuousAt (ε / 2) (half_pos hε)
  refine ⟨min r s, lt_min hr hs, ?_⟩
  rintro ⟨z, u⟩ ⟨hz, hu⟩ hdist
  have hzx : dist z x < r :=
    (le_max_left (dist z x) (dist u t)).trans_lt
      (by simpa only [Prod.dist_eq] using hdist.trans_le (min_le_left _ _))
  have hut : dist u t < s :=
    (le_max_right (dist z x) (dist u t)).trans_lt
      (by simpa only [Prod.dist_eq] using hdist.trans_le (min_le_right _ _))
  calc
    dist (Y z u) (Y x t) ≤ dist (Y z u) (Y x u) + dist (Y x u) (Y x t) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add
      (by simpa only [dist_eq_norm] using hparam z hz hzx u hu) (htime hut)
    _ = ε := add_halves ε

end FirstVariationalDefect
