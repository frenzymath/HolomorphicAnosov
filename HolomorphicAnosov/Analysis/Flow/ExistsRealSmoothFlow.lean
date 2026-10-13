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
import HolomorphicAnosov.Analysis.Flow.ExistsRealC1LocalFlow
import HolomorphicAnosov.Analysis.Flow.ContDiffOnOfLocalFamilies
import HolomorphicAnosov.Analysis.Flow.ExistsRealFiniteFlow

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology _root_.Topology NNReal

namespace HolomorphicAnosov.W07FiniteFlowBootstrap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smooth real field has a jointly smooth actual local family on ONE rectangle.
The rectangle is chosen once by C1 existence. For every finite order, continuation identifies
finite-order local families with that SAME family on the entire fixed rectangle.
Source: Teschl Theorems2.10 and6.1, pp.46–47 and189–190. -/
theorem exists_real_smooth_flow [FiniteDimensional ℝ E]
    (F : E → E) (Ω : Set E) (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ ∞ F Ω)
    (x : E) (hx : x ∈ Ω) :
    ∃ (U : Set E) (δ : ℝ) (Φ : E × ℝ → E),
      IsOpen U ∧ x ∈ U ∧ 0 < δ ∧ ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo (-δ) δ) ∧
      (∀ w ∈ U, Φ (w, 0) = w) ∧
      (∀ w ∈ U, ∀ t ∈ Ioo (-δ) δ,
        HasDerivAt (fun r ↦ Φ (w, r)) (F (Φ (w, t))) t) ∧
      (∀ w ∈ U, ∀ t ∈ Ioo (-δ) δ, Φ (w, t) ∈ Ω) := by
  have hF1 : ContDiffOn ℝ 1 F Ω := hF.of_le (by simp)
  obtain ⟨r, hr, δ, hδ, Φ, Y, hΦ, hY, hzero, hmem, htime, hder, happly⟩ :=
    RealC1FlowExistence.exists_real_c1_local_flow F Ω hΩ hF1 x hx
  let U := ball x r
  let J := Ioo (-δ) δ
  have hn (n : ℕ) : ContDiffOn ℝ (n + 1) Φ (U ×ˢ J) :=
    W07FiniteFlowContinuation.contDiffOn_of_local_families hΩ hF1 (n + 1)
      (fun q hq ↦ exists_real_finite_flow n F Ω hΩ (hF.of_le (by simp)) q hq)
      isOpen_ball isOpen_Ioo ordConnected_Ioo ⟨by linarith, hδ⟩ hΦ.continuousOn
      (contDiffOn_id.congr (fun w hw ↦ hzero w hw))
      (fun w hw t ht ↦ htime (w, t) ⟨hw, ht⟩)
      (fun w hw t ht ↦ hmem (w, t) ⟨hw, ht⟩)
  refine ⟨U, δ, Φ, isOpen_ball, by simpa [U], hδ, ?_, hzero,
    (fun w hw t ht ↦ htime (w, t) ⟨hw, ht⟩),
    (fun w hw t ht ↦ hmem (w, t) ⟨hw, ht⟩)⟩
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_infty.mpr
  intro n
  exact ((hn n).of_le (by simp)).contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds hp)

end HolomorphicAnosov.W07FiniteFlowBootstrap
