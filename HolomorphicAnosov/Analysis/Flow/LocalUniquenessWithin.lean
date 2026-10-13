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
import HolomorphicAnosov.Analysis.Flow.RealFlowLocalUniqueness

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

omit [FiniteDimensional ℝ E] [T2Space N] in
/-- Andrews uniqueness, including endpoints: use one actual chart near the
common value and the proved real within-interval uniqueness kernel. -/
theorem local_uniqueness_within
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I N)))
    {J : Set ℝ} (hJ : OrdConnected J) {γ γ' : ℝ → N}
    (hγ : IsMIntegralCurveOn (I := I) γ V J)
    (hγ' : IsMIntegralCurveOn (I := I) γ' V J)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) (heq : γ t₀ = γ' t₀) :
    ∀ᶠ t in nhdsWithin t₀ J, γ t = γ' t := by
  let e := extChartAt I (γ t₀)
  let F : E → E := fun q ↦
    tangentCoordChange I (e.symm q) (γ t₀) (e.symm q) (V (e.symm q))
  have hv := (hV.of_le (show (1 : ℕ∞) ≤ ∞ by simp)).contMDiffAt (x := γ t₀)
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  obtain ⟨K, B, hB, hLip⟩ : ∃ K, ∃ B ∈ nhds (e (γ t₀)), LipschitzOnWith K F B :=
    (hv.contDiffAt (range_mem_nhds_isInteriorPoint
      (BoundarylessManifold.isInteriorPoint (I := I) (x := γ t₀)))).snd.exists_lipschitzOnWith
  have hsrc : e.source ∈ nhds (γ t₀) := extChartAt_source_mem_nhds (I := I) _
  have hγsrc := (hγ.continuousWithinAt ht₀) hsrc
  have hγ'src := (hγ'.continuousWithinAt ht₀) (heq ▸ hsrc)
  obtain ⟨ε, hε, hbox⟩ := Metric.mem_nhdsWithin_iff.mp (Filter.inter_mem hγsrc hγ'src)
  let A := Metric.ball t₀ ε ∩ J
  have hA : OrdConnected A := by
    simpa only [A, Real.ball_eq_Ioo] using
      (ordConnected_Ioo (a := t₀ - ε) (b := t₀ + ε)).inter hJ
  have htA : t₀ ∈ A := ⟨Metric.mem_ball_self hε, ht₀⟩
  have hmem : ∀ t ∈ A, γ t ∈ e.source ∧ γ' t ∈ e.source := hbox
  have hd {g : ℝ → N} (hg : IsMIntegralCurveOn (I := I) g V J)
      (hg0 : g t₀ = γ t₀)
      (hs : ∀ t ∈ A, g t ∈ e.source) :
      ∀ t ∈ A, HasDerivWithinAt (e ∘ g) (F (e (g t))) A t := by
    intro t ht
    have hder := (hg.mono inter_subset_right).hasDerivWithinAt
      (t₀ := t₀) ht (by simpa only [hg0] using hs t ht)
    rw [hg0] at hder
    change HasDerivWithinAt (e ∘ g)
      (tangentCoordChange I (e.symm (e (g t))) (γ t₀) (e.symm (e (g t)))
        (V (e.symm (e (g t))))) A t
    rw [e.left_inv (hs t ht)]
    exact hder
  have hdγ := hd hγ rfl (fun t ht ↦ (hmem t ht).1)
  have hdγ' := hd hγ' heq.symm (fun t ht ↦ (hmem t ht).2)
  have hcγ : ContinuousOn (e ∘ γ) A :=
    fun t ht ↦ (hdγ t ht).continuousWithinAt
  have hcγ' : ContinuousOn (e ∘ γ') A :=
    fun t ht ↦ (hdγ' t ht).continuousWithinAt
  have hlocal := HolomorphicAnosov.RealFlowUniqueness.local_uniqueness
    hA hcγ hcγ' hdγ hdγ' htA (congrArg e heq) hB hLip
  have hnhds : nhdsWithin t₀ A = nhdsWithin t₀ J :=
    nhdsWithin_inter_of_mem (nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hε))
  rw [hnhds] at hlocal
  have hAmem : A ∈ nhdsWithin t₀ J := Filter.inter_mem
    (nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hε)) self_mem_nhdsWithin
  filter_upwards [hlocal, hAmem] with t ht htA
  exact e.injOn (hmem t htA).1 (hmem t htA).2 ht

end HolomorphicAnosov.SmoothLocalFlowProof
