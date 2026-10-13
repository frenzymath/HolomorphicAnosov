import HolomorphicAnosov.Analysis.Flow.UniformTaylorRemainder
import HolomorphicAnosov.Analysis.Flow.NormalizedDefectBound
import HolomorphicAnosov.Analysis.Flow.GronwallForcingHomogeneous
import HolomorphicAnosov.Analysis.Flow.HasFDerivAtInitialOfVariationalOde
import HolomorphicAnosov.Analysis.Flow.HasDerivAtIntegralEq
import HolomorphicAnosov.Analysis.Flow.HasFDerivAtInitialOfVariationalOdeNegative
import HolomorphicAnosov.Analysis.Flow.HasFDerivAtInitialOfIntegralWitnesses
import HolomorphicAnosov.Analysis.Flow.LinearIvpNormBound
import HolomorphicAnosov.Analysis.Flow.LinearIvpStability
import HolomorphicAnosov.Analysis.Flow.CoefficientsUniformNearInitial
import HolomorphicAnosov.Analysis.Flow.LinearIvpUniformNearInitial
import HolomorphicAnosov.Analysis.Flow.LinearIvpJointContinuousOn
import HolomorphicAnosov.Analysis.Flow.FirstVariationAndJointDerivativeContinuity
import HolomorphicAnosov.Analysis.Flow.LinearIvpJointContinuousOnSymmetric
import HolomorphicAnosov.Analysis.Flow.FirstVariationAndJointDerivativeContinuitySymmetric
import HolomorphicAnosov.Analysis.Flow.FirstVariationOfJointIntegralWitnesses
import HolomorphicAnosov.Analysis.Flow.ExistsPicardFamilyWithRange
import HolomorphicAnosov.Analysis.Flow.ExistsLinearIntegralFamily
import HolomorphicAnosov.Analysis.Flow.ExistsPicardVariationalIntegralWitnesses
import HolomorphicAnosov.Analysis.JointRealPartialDerivative
import HolomorphicAnosov.Analysis.JointRealC1
import HolomorphicAnosov.Analysis.Flow.ExistsRealC1PartialFlow
import HolomorphicAnosov.Analysis.Flow.ExistsRealJointDerivativeFlow
import HolomorphicAnosov.Analysis.Flow.ExistsRealC1LocalFlow
import HolomorphicAnosov.Analysis.Flow.AugmentedField
import HolomorphicAnosov.Analysis.Flow.AugmentedFieldContDiffOn
import HolomorphicAnosov.Analysis.Flow.JointDerivative
import HolomorphicAnosov.Analysis.Flow.JointDerivativeApply
import HolomorphicAnosov.Analysis.Flow.JointDerivativeContDiffOn
import HolomorphicAnosov.Analysis.Flow.FiniteOrderSuccessor
import HolomorphicAnosov.Analysis.Flow.AugmentedTrajectoryEq
import HolomorphicAnosov.Analysis.Flow.VariationalRegularOfAugmented
import HolomorphicAnosov.Analysis.Flow.SmoothAtAllFiniteOrders
import HolomorphicAnosov.Analysis.Flow.SuccessorOnSameSolutionOfAugmented
import HolomorphicAnosov.Analysis.Flow.JointDerivativeEqCoprod
import HolomorphicAnosov.Analysis.Flow.SmoothOnAllFiniteGerms
import HolomorphicAnosov.Analysis.Flow.RealFlowLocalUniqueness
import HolomorphicAnosov.Analysis.Flow.RealFlowEqOn
import HolomorphicAnosov.Analysis.Flow.IndividualLocalExistence
import HolomorphicAnosov.Analysis.Flow.LocalGroupFromIntegralCurves
import HolomorphicAnosov.Analysis.Flow.LocalUniquenessWithin
import HolomorphicAnosov.Analysis.Flow.UniquenessOnOrdConnected
import HolomorphicAnosov.Analysis.Flow.TimeSliceInjective
import HolomorphicAnosov.Analysis.Flow.TimeSliceSmooth
import HolomorphicAnosov.Analysis.Flow.VariationalOperatorBijective
import HolomorphicAnosov.Analysis.Flow.RestartEq
import HolomorphicAnosov.Analysis.Flow.ContDiffOnOfLocalFamilies
import HolomorphicAnosov.Analysis.Flow.ExistsC1VariationalFlow
import HolomorphicAnosov.Analysis.Flow.ExistsRealFiniteFlow
import HolomorphicAnosov.Analysis.Flow.ExistsRealSmoothFlow
import HolomorphicAnosov.Analysis.Flow.CoordinateFieldSmooth
import HolomorphicAnosov.Analysis.Flow.ExistsManifoldSmoothFamily
import HolomorphicAnosov.Analysis.Flow.TimeSliceLocalDiffeomorph
import HolomorphicAnosov.Analysis.TeschlCompactIntervalLinearODE
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


/-! This file proves existence, regularity, uniqueness, and group-law properties of smooth local flows for smooth vector fields, including the required finite-order ODE arguments (Andrews, Lecture 6; Teschl, Thms. 2.9–2.10). -/

open Set
open scoped Manifold ContDiff







open Set Filter
open scoped Topology _root_.Topology NNReal

namespace FirstVariationalDefect

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end FirstVariationalDefect




open Set Function ODE Metric
open scoped Topology _root_.Topology NNReal

namespace PicardVariationalWitnesses

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end PicardVariationalWitnesses


namespace HolomorphicAnosov.JointRealC1Scratch

open Set Filter
open scoped Topology _root_.Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end HolomorphicAnosov.JointRealC1Scratch

namespace RealC1FlowExistence

open Set Filter
open scoped Topology _root_.Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end RealC1FlowExistence





noncomputable section

open Set
open scoped ContDiff Topology _root_.Topology

namespace SmoothFlowBootstrap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end SmoothFlowBootstrap



open Set Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.RealFlowUniqueness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end HolomorphicAnosov.RealFlowUniqueness

namespace HolomorphicAnosov.SmoothLocalFlowProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [BoundarylessManifold I N] [T2Space N]
  {V : (x : N) → TangentSpace I x}

end HolomorphicAnosov.SmoothLocalFlowProof

namespace HolomorphicAnosov.SmoothLocalFlowProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

end HolomorphicAnosov.SmoothLocalFlowProof


namespace HolomorphicAnosov.W07FiniteFlowContinuation

open Set Filter
open scoped ContDiff Topology _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

end HolomorphicAnosov.W07FiniteFlowContinuation


universe u

namespace HolomorphicAnosov.W07FiniteFlowBootstrap

open Set Filter
open scoped ContDiff Topology _root_.Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end
end HolomorphicAnosov.W07FiniteFlowBootstrap



namespace HolomorphicAnosov.W07ManifoldFlow

open Set Filter
open scoped Manifold ContDiff Topology _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [BoundarylessManifold I N] [T2Space N]
  {V : (x : N) → TangentSpace I x}

/-- A local-flow rectangle can be shrunk so that its endpoints lie in the prescribed initial-point neighborhood (Andrews, §6.5). -/
private theorem exists_complete_local_flow
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I N))) (z : N) :
    ∃ (U : Set N) (δ : ℝ) (Ψ : N × ℝ → N),
      IsOpen U ∧ z ∈ U ∧ 0 < δ ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ Ψ (U ×ˢ Ioo (-δ) δ) ∧
      (∀ y ∈ U, Ψ (y, 0) = y) ∧
      (∀ y ∈ U, IsMIntegralCurveOn (I := I) (fun t ↦ Ψ (y, t)) V (Ioo (-δ) δ)) ∧
      (∀ (J : Set ℝ) (_ : OrdConnected J) (t₀ : ℝ) (_ : t₀ ∈ J) (γ γ' : ℝ → N),
        IsMIntegralCurveOn (I := I) γ V J → IsMIntegralCurveOn (I := I) γ' V J →
        γ t₀ = γ' t₀ → EqOn γ γ' J) ∧
      (∀ y ∈ U, ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-δ) δ,
        s + t ∈ Ioo (-δ) δ → Ψ (y, s) ∈ U → Ψ (Ψ (y, s), t) = Ψ (y, s + t)) ∧
      (∀ t ∈ Ioo (-δ) δ, IsLocalDiffeomorphOn I I ∞ (fun y ↦ Ψ (y, t)) U) := by
  obtain ⟨A, ε, Ψ, hA, hzA, hε, hΨ, hzero, hcurve⟩ := exists_manifold_smooth_family hV z
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hc : ContinuousAt Ψ (z, 0) :=
    hΨ.continuousOn.continuousAt ((hA.prod isOpen_Ioo).mem_nhds ⟨hzA, h0⟩)
  have hn : Ψ ⁻¹' A ∈ nhds (z, 0) :=
    hc.preimage_mem_nhds (hA.mem_nhds (by simpa only [hzero z hzA] using hzA))
  obtain ⟨S, hS, T, hT, hST⟩ := mem_nhds_prod_iff.mp hn
  obtain ⟨W, hWS, hW, hzW⟩ := mem_nhds_iff.mp hS
  obtain ⟨r, hr, hrT⟩ := Metric.mem_nhds_iff.mp hT
  let U := W ∩ A
  let δ := min ε r / 2
  have hδ : 0 < δ := half_pos (lt_min hε hr)
  have hδε : δ < ε := lt_of_lt_of_le (half_lt_self (lt_min hε hr)) (min_le_left ..)
  have hδr : δ < r := lt_of_lt_of_le (half_lt_self (lt_min hε hr)) (min_le_right ..)
  have hsub : Ioo (-δ) δ ⊆ Ioo (-ε) ε := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hstay (y : N) (hy : y ∈ U) (t : ℝ) (ht : t ∈ Ioo (-δ) δ) : Ψ (y, t) ∈ A := by
    apply hST
    refine ⟨hWS hy.1, hrT ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨U, δ, Ψ, hW.inter hA, ⟨hzW, hzA⟩, hδ,
    hΨ.mono (prod_mono inter_subset_right hsub),
    (fun y hy ↦ hzero y hy.2), (fun y hy ↦ (hcurve y hy.2).mono hsub), ?_, ?_, ?_⟩
  · intro J hJ t₀ ht₀ γ γ' hγ hγ' heq
    exact SmoothLocalFlowProof.uniqueness_on_ordConnected hV hJ hγ hγ' ht₀ heq
  · intro y hy s hs t ht hst hys
    exact SmoothLocalFlowProof.local_group_from_integral_curves hV hε hzero hcurve
      hy.2 (hsub hs) (hsub ht) (hsub hst) hys.2
  · intro t ht y
    exact time_slice_local_diffeomorph hV hA hε hΨ hzero hcurve (hsub ht) y.property.2
      (hstay y y.property t ht)

end HolomorphicAnosov.W07ManifoldFlow



namespace HolomorphicAnosov

/-- Every smooth vector field on a finite-dimensional manifold admits a jointly smooth local flow with the usual integral-curve, uniqueness, group-law, and local-diffeomorphism properties (Andrews, Lecture 6; Teschl, Thms. 2.9–2.10). -/
theorem exists_smoothLocalFlow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] [BoundarylessManifold I N] [T2Space N]
    (V : (x : N) → TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I N)))
    (z : N) :
    ∃ (U : Set N) (δ : ℝ) (Ψ : N × ℝ → N),
      IsOpen U ∧ z ∈ U ∧ 0 < δ ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ Ψ (U ×ˢ Ioo (-δ) δ) ∧
      (∀ y ∈ U, Ψ (y, 0) = y) ∧
      (∀ y ∈ U, IsMIntegralCurveOn (I := I) (fun t ↦ Ψ (y, t)) V (Ioo (-δ) δ)) ∧
      (∀ (J : Set ℝ) (_ : OrdConnected J) (t₀ : ℝ) (_ : t₀ ∈ J)
          (γ γ' : ℝ → N),
        IsMIntegralCurveOn (I := I) γ V J →
        IsMIntegralCurveOn (I := I) γ' V J →
        γ t₀ = γ' t₀ → EqOn γ γ' J) ∧
      (∀ y ∈ U, ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Ioo (-δ) δ,
        s + t ∈ Ioo (-δ) δ → Ψ (y, s) ∈ U →
        Ψ (Ψ (y, s), t) = Ψ (y, s + t)) ∧
      (∀ t ∈ Ioo (-δ) δ,
        IsLocalDiffeomorphOn I I ∞ (fun y ↦ Ψ (y, t)) U) := by
  exact W07ManifoldFlow.exists_complete_local_flow hV z


end HolomorphicAnosov

