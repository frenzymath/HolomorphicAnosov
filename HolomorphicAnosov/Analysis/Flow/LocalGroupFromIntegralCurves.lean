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

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology _root_.Topology NNReal

namespace HolomorphicAnosov.SmoothLocalFlowProof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [BoundarylessManifold I N] [T2Space N]
  {V : (x : N) → TangentSpace I x}

omit [FiniteDimensional ℝ E] in
/-- Andrews §6.4: compare a restarted curve with a time translate on their
common open time interval. Both 0 and the requested time lie in that interval.
No intervening trajectory is required to stay in the initial neighborhood. -/
theorem local_group_from_integral_curves
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I N)))
    {U : Set N} {δ : ℝ} {Ψ : N × ℝ → N}
    (hδ : 0 < δ)
    (hzero : ∀ y ∈ U, Ψ (y, 0) = y)
    (hcurve : ∀ y ∈ U,
      IsMIntegralCurveOn (I := I) (fun t ↦ Ψ (y, t)) V (Ioo (-δ) δ))
    {y : N} (hy : y ∈ U) {s t : ℝ}
    (hs : s ∈ Ioo (-δ) δ) (ht : t ∈ Ioo (-δ) δ)
    (hst : s + t ∈ Ioo (-δ) δ) (hys : Ψ (y, s) ∈ U) :
    Ψ (Ψ (y, s), t) = Ψ (y, s + t) := by
  let a := max (-δ) (-δ - s)
  let b := min δ (δ - s)
  have h0 : (0 : ℝ) ∈ Ioo a b := by
    dsimp [a, b]
    rcases hs with ⟨hs₁, hs₂⟩
    constructor
    · exact max_lt (by linarith) (by linarith)
    · exact lt_min hδ (by linarith)
  have ht' : t ∈ Ioo a b := by
    dsimp [a, b]
    rcases ht with ⟨ht₁, ht₂⟩
    rcases hst with ⟨hst₁, hst₂⟩
    constructor
    · exact max_lt ht₁ (by linarith)
    · exact lt_min ht₂ (by linarith)
  have hsub : Ioo a b ⊆ Ioo (-δ) δ := by
    intro u hu
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hu.1,
      lt_of_lt_of_le hu.2 (min_le_left _ _)⟩
  have hshift : Ioo a b ⊆ {u : ℝ | u + s ∈ Ioo (-δ) δ} := by
    intro u hu
    have hu₁ := lt_of_le_of_lt (le_max_right (-δ) (-δ - s)) hu.1
    have hu₂ := lt_of_lt_of_le hu.2 (min_le_right δ (δ - s))
    exact ⟨by linarith, by linarith⟩
  have hleft := (hcurve _ hys).mono hsub
  have hright := ((hcurve y hy).comp_add s).mono hshift
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (I := I) h0 (hV.of_le (by simp)) hleft hright
    (by simpa using hzero (Ψ (y, s)) hys)
  simpa [Function.comp_apply, add_comm] using heq ht'

end HolomorphicAnosov.SmoothLocalFlowProof
