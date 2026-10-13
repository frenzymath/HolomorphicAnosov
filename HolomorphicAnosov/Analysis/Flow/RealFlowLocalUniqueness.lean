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

namespace HolomorphicAnosov.RealFlowUniqueness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Local equality follows from one Lipschitz neighborhood of the common
value. Continuity supplies a small TIME neighborhood for both actual curves;
closed subsegments stay inside the actual order-connected interval. -/
theorem local_uniqueness
    {F : E → E} {J : Set ℝ} (hJ : OrdConnected J) {f g : ℝ → E}
    (hf : ContinuousOn f J) (hg : ContinuousOn g J)
    (hdf : ∀ t ∈ J, HasDerivWithinAt f (F (f t)) J t)
    (hdg : ∀ t ∈ J, HasDerivWithinAt g (F (g t)) J t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) (heq : f t₀ = g t₀)
    {B : Set E} (hB : B ∈ nhds (f t₀)) {K : NNReal} (hLip : LipschitzOnWith K F B) :
    ∀ᶠ t in nhdsWithin t₀ J, f t = g t := by
  have hfb : f ⁻¹' B ∈ nhdsWithin t₀ J := (hf t₀ ht₀) hB
  have hgb : g ⁻¹' B ∈ nhdsWithin t₀ J :=
    (hg t₀ ht₀) (heq ▸ hB)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp (inter_mem hfb hgb)
  apply mem_of_superset (inter_mem (nhdsWithin_le_nhds (Metric.ball_mem_nhds t₀ hε))
    self_mem_nhdsWithin)
  intro t ht
  rcases lt_trichotomy t t₀ with hlt | rfl | hgt
  · have hsub : Icc t t₀ ⊆ J := hJ.out ht.2 ht₀
    have hbuf : ∀ s ∈ Icc t t₀, f s ∈ B ∧ g s ∈ B := by
      intro s hs
      apply hball ⟨?_, hsub hs⟩
      have hdist : |t - t₀| < ε := by simpa [Metric.mem_ball, Real.dist_eq] using ht.1
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_of_nonpos (sub_nonpos.mpr hs.2)]
      have hdt := (abs_lt.mp hdist).1
      linarith [hs.1, hs.2]
    have hright (s : ℝ) (hs : s ∈ Ioc t t₀) : J ∈ nhdsWithin s (Iic s) :=
      mem_of_superset (Icc_mem_nhdsLE_of_mem hs) hsub
    exact ODE_solution_unique_of_mem_Icc_left
      (fun _ _ ↦ hLip) (hf.mono hsub)
      (fun s hs ↦ (hdf s (hsub (Ioc_subset_Icc_self hs))).mono_of_mem_nhdsWithin
        (hright s hs))
      (fun s hs ↦ (hbuf s (Ioc_subset_Icc_self hs)).1)
      (hg.mono hsub)
      (fun s hs ↦ (hdg s (hsub (Ioc_subset_Icc_self hs))).mono_of_mem_nhdsWithin
        (hright s hs))
      (fun s hs ↦ (hbuf s (Ioc_subset_Icc_self hs)).2) heq ⟨le_rfl, hlt.le⟩
  · exact heq
  · have hsub : Icc t₀ t ⊆ J := hJ.out ht₀ ht.2
    have hbuf : ∀ s ∈ Icc t₀ t, f s ∈ B ∧ g s ∈ B := by
      intro s hs
      apply hball ⟨?_, hsub hs⟩
      have hdist : |t - t₀| < ε := by simpa [Metric.mem_ball, Real.dist_eq] using ht.1
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
      have hdt := (abs_lt.mp hdist).2
      linarith [hs.1, hs.2]
    have hleft (s : ℝ) (hs : s ∈ Ico t₀ t) : J ∈ nhdsWithin s (Ici s) :=
      mem_of_superset (Icc_mem_nhdsGE_of_mem hs) hsub
    exact ODE_solution_unique_of_mem_Icc_right
      (fun _ _ ↦ hLip) (hf.mono hsub)
      (fun s hs ↦ (hdf s (hsub (Ico_subset_Icc_self hs))).mono_of_mem_nhdsWithin
        (hleft s hs))
      (fun s hs ↦ (hbuf s (Ico_subset_Icc_self hs)).1)
      (hg.mono hsub)
      (fun s hs ↦ (hdg s (hsub (Ico_subset_Icc_self hs))).mono_of_mem_nhdsWithin
        (hleft s hs))
      (fun s hs ↦ (hbuf s (Ico_subset_Icc_self hs)).2) heq ⟨hgt.le, le_rfl⟩

end HolomorphicAnosov.RealFlowUniqueness
