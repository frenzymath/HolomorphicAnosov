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
import HolomorphicAnosov.Analysis.Flow.LinearIvpJointContinuousOn

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace FirstVariationalDefect
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two-sided joint continuity of an actual linear IVP. Negative times reverse both the
coefficient and trajectory. The two closed time halves are pasted at their shared zero-time
slice; the initial set remains open and need not be compact or closed. -/
theorem linear_ivp_joint_continuousOn_symmetric
    (A : E × ℝ → E →L[ℝ] E) (Y : E → ℝ → E →L[ℝ] E)
    (U : Set E) (I : Set ℝ) (hU : IsOpen U) (hI : IsOpen I)
    (hAcont : ContinuousOn A (U ×ˢ I))
    (T : ℝ) (hT : 0 < T) (hseg : Icc (-T) T ⊆ I) (K : ℝ≥0)
    (hA : ∀ z ∈ U, ∀ t ∈ Icc (-T) T, ‖A (z, t)‖ ≤ K)
    (hY : ∀ z ∈ U, ∀ t ∈ Icc (-T) T,
      HasDerivAt (Y z) ((A (z, t)).comp (Y z t)) t)
    (L : E →L[ℝ] E) (hinit : ∀ z ∈ U, Y z 0 = L) :
    ContinuousOn (fun p : E × ℝ ↦ Y p.1 p.2) (U ×ˢ Icc (-T) T) := by
  have hpos : Icc 0 T ⊆ Icc (-T) T := fun _ hs ↦
    ⟨(neg_nonpos.mpr hT.le).trans hs.1, hs.2⟩
  have hrev : ∀ t ∈ Icc 0 T, -t ∈ Icc (-T) T := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hp := linear_ivp_joint_continuousOn A Y U I hU hI hAcont T hT.le
    (hpos.trans hseg) K (fun z hz t ht ↦ hA z hz t (hpos ht))
    (fun z hz t ht ↦ hY z hz t (hpos ht)) L hinit
  let R : E × ℝ → E × ℝ := fun p ↦ (p.1, -p.2)
  have hR : Continuous R := continuous_fst.prodMk continuous_snd.neg
  have hncoef : ContinuousOn (fun p : E × ℝ ↦ -A (p.1, -p.2))
      (U ×ˢ (Neg.neg ⁻¹' I)) :=
    (hAcont.comp hR.continuousOn (fun _ hp ↦ ⟨hp.1, hp.2⟩)).neg
  have hn := linear_ivp_joint_continuousOn
    (fun p : E × ℝ ↦ -A (p.1, -p.2)) (fun z t ↦ Y z (-t))
    U (Neg.neg ⁻¹' I) hU (hI.preimage continuous_neg) hncoef T hT.le
    (fun t ht ↦ hseg (hrev t ht)) K
    (fun z hz t ht ↦ by simpa using hA z hz (-t) (hrev t ht))
    (fun z hz t ht ↦ by
      simpa [Function.comp_def] using
        (hY z hz (-t) (hrev t ht)).scomp t (hasDerivAt_neg t)) L
    (fun z hz ↦ by simpa using hinit z hz)
  have hn' : ContinuousOn (fun p : E × ℝ ↦ Y p.1 p.2) (U ×ˢ Icc (-T) 0) := by
    have hm : MapsTo R (U ×ˢ Icc (-T) 0) (U ×ˢ Icc 0 T) := by
      rintro ⟨z, t⟩ ⟨hz, ht⟩
      refine ⟨hz, ?_⟩
      dsimp [R]
      constructor <;> linarith [ht.1, ht.2]
    simpa [R, Function.comp_def] using hn.comp hR.continuousOn hm
  have hclosedp : IsClosed ((univ : Set E) ×ˢ Icc 0 T) :=
    isClosed_univ.prod isClosed_Icc
  have hclosedn : IsClosed ((univ : Set E) ×ˢ Icc (-T) 0) :=
    isClosed_univ.prod isClosed_Icc
  have hclp : closure (U ×ˢ Icc 0 T) ⊆ (univ : Set E) ×ˢ Icc 0 T := by
    exact (closure_mono (prod_mono (subset_univ U) Subset.rfl)).trans_eq hclosedp.closure_eq
  have hcln : closure (U ×ˢ Icc (-T) 0) ⊆ (univ : Set E) ×ˢ Icc (-T) 0 := by
    exact (closure_mono (prod_mono (subset_univ U) Subset.rfl)).trans_eq hclosedn.closure_eq
  intro p hpall
  have hpc : ContinuousWithinAt (fun p : E × ℝ ↦ Y p.1 p.2) (U ×ˢ Icc 0 T) p := by
    by_cases ht : 0 ≤ p.2
    · exact hp p ⟨hpall.1, ht, hpall.2.2⟩
    · apply continuousWithinAt_of_notMem_closure
      intro hc
      exact ht (hclp hc).2.1
  have hnc : ContinuousWithinAt (fun p : E × ℝ ↦ Y p.1 p.2) (U ×ˢ Icc (-T) 0) p := by
    by_cases ht : p.2 ≤ 0
    · exact hn' p ⟨hpall.1, hpall.2.1, ht⟩
    · apply continuousWithinAt_of_notMem_closure
      intro hc
      exact ht (hcln hc).2.2
  apply (hpc.union hnc).mono
  intro q hq
  by_cases ht : 0 ≤ q.2
  · exact Or.inl ⟨hq.1, ht, hq.2.2⟩
  · exact Or.inr ⟨hq.1, hq.2.1, le_of_not_ge ht⟩

end FirstVariationalDefect
