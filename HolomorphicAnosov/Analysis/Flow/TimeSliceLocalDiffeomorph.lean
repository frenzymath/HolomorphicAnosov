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
import HolomorphicAnosov.Analysis.Flow.LocalGroupFromIntegralCurves
import HolomorphicAnosov.Analysis.Flow.TimeSliceSmooth

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology _root_.Topology NNReal

namespace HolomorphicAnosov.W07ManifoldFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [BoundarylessManifold I N] [T2Space N]
  {V : (x : N) → TangentSpace I x}

omit [FiniteDimensional ℝ E] in
/-- Actual reverse-time local inverses on guarded source and target sets.
Source: Andrews §6.5: the group law supplies both inverse identities, and smoothness follows
by taking the two time slices of the same original smooth family. -/
theorem time_slice_local_diffeomorph
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I N)))
    {A : Set N} (hA : IsOpen A) {δ : ℝ} (hδ : 0 < δ) {Ψ : N × ℝ → N}
    (hΨ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ Ψ (A ×ˢ Ioo (-δ) δ))
    (hzero : ∀ w ∈ A, Ψ (w, 0) = w)
    (hcurve : ∀ w ∈ A, IsMIntegralCurveOn (fun t ↦ Ψ (w, t)) V (Ioo (-δ) δ))
    {t : ℝ} (ht : t ∈ Ioo (-δ) δ) {y : N} (hy : y ∈ A) (hyt : Ψ (y, t) ∈ A) :
    IsLocalDiffeomorphAt I I ∞ (fun w ↦ Ψ (w, t)) y := by
  let G : N → N := fun w ↦ Ψ (w, t)
  let F : N → N := fun w ↦ Ψ (w, -t)
  have hnt : -t ∈ Ioo (-δ) δ := by constructor <;> linarith [ht.1, ht.2]
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hG : ContMDiffOn I I ∞ G A := SmoothLocalFlowProof.time_slice_smooth hΨ ht
  have hF : ContMDiffOn I I ∞ F A := SmoothLocalFlowProof.time_slice_smooth hΨ hnt
  have hFG (w : N) (hw : w ∈ A) (hGw : G w ∈ A) : F (G w) = w := by
    have hh := SmoothLocalFlowProof.local_group_from_integral_curves hV hδ hzero hcurve
      hw ht hnt (by simpa only [add_neg_cancel] using h0) hGw
    simpa only [G, F, add_neg_cancel, hzero w hw] using hh
  have hGF (w : N) (hw : w ∈ A) (hFw : F w ∈ A) : G (F w) = w := by
    have hh := SmoothLocalFlowProof.local_group_from_integral_curves hV hδ hzero hcurve
      hw hnt ht (by simpa only [neg_add_cancel] using h0) hFw
    simpa only [G, F, neg_add_cancel, hzero w hw] using hh
  let B := A ∩ F ⁻¹' A
  let C := A ∩ G ⁻¹' B
  have hB : IsOpen B := hF.continuousOn.isOpen_inter_preimage hA hA
  have hC : IsOpen C := hG.continuousOn.isOpen_inter_preimage hA hB
  have hyC : y ∈ C := ⟨hy, hyt, by change F (G y) ∈ A; rw [hFG y hy hyt]; exact hy⟩
  let p : PartialDiffeomorph I I N N ∞ :=
    { toFun := G
      invFun := F
      source := C
      target := B
      map_source' := fun w hw ↦ hw.2
      map_target' := fun w hw ↦ ⟨hw.2, by change G (F w) ∈ B; rw [hGF w hw.1 hw.2]; exact hw⟩
      left_inv' := fun w hw ↦ hFG w hw.1 hw.2.1
      right_inv' := fun w hw ↦ hGF w hw.1 hw.2
      open_source := hC
      open_target := hB
      contMDiffOn_toFun := hG.mono inter_subset_left
      contMDiffOn_invFun := hF.mono inter_subset_left }
  exact ⟨p, hyC, fun _ _ ↦ rfl⟩

end HolomorphicAnosov.W07ManifoldFlow
