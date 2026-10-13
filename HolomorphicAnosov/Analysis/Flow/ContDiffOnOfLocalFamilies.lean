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
import HolomorphicAnosov.Analysis.Flow.RestartEq

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology _root_.Topology NNReal

namespace HolomorphicAnosov.W07FiniteFlowContinuation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Given local C^n existence at every point of the original open field domain, an actual
continuous integral family is C^n on its ENTIRE original open rectangle. Finite guarded
restart compositions propagate endpoint certificates along each connected trajectory.
Source: Teschl Theorem6.1, pp.189–190. No smooth-flow theorem is used. -/
theorem contDiffOn_of_local_families
    {F : E → E} {Ω : Set E} (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ 1 F Ω)
    (n : ℕ) (hlocal : ∀ q ∈ Ω,
      ∃ (A : Set E) (δ : ℝ) (Ψ : E × ℝ → E), IsOpen A ∧ q ∈ A ∧ 0 < δ ∧
        ContDiffOn ℝ n Ψ (A ×ˢ Ioo (-δ) δ) ∧
        (∀ w ∈ A, Ψ (w, 0) = w) ∧
        (∀ w ∈ A, ∀ r ∈ Ioo (-δ) δ,
          HasDerivAt (fun t ↦ Ψ (w, t)) (F (Ψ (w, r))) r) ∧
        (∀ w ∈ A, ∀ r ∈ Ioo (-δ) δ, Ψ (w, r) ∈ Ω))
    {U : Set P} (hU : IsOpen U) {J : Set ℝ} (hJ : IsOpen J)
    (hcJ : OrdConnected J) (h0 : 0 ∈ J) {α : P × ℝ → E}
    (hcont : ContinuousOn α (U ×ˢ J)) (hzero : ContDiffOn ℝ n (fun w ↦ α (w, 0)) U)
    (hα : ∀ w ∈ U, ∀ r ∈ J, HasDerivAt (fun t ↦ α (w, t)) (F (α (w, r))) r)
    (hαΩ : ∀ w ∈ U, ∀ r ∈ J, α (w, r) ∈ Ω) :
    ContDiffOn ℝ n α (U ×ˢ J) := by
  classical
  intro p hp
  let C : Set ℝ := {s | ∃ W, IsOpen W ∧ p.1 ∈ W ∧ W ⊆ U ∧ ∃ G : P → E,
    ContDiffOn ℝ n G W ∧ EqOn G (fun w ↦ α (w, s)) W}
  have htransfer (r : ℝ) (hr : r ∈ J) :
      ∃ O, IsOpen O ∧ r ∈ O ∧ O ⊆ J ∧
        ∀ s ∈ O, ∀ t ∈ O, s ∈ C → t ∈ C := by
    obtain ⟨A, δ, Ψ, hA, hqA, hδ, hΨ, hΨzero, hΨcurve, hΨΩ⟩ :=
      hlocal (α (p.1, r)) (hαΩ p.1 hp.1 r hr)
    have hγc : ContinuousOn (fun t ↦ α (p.1, t)) J :=
      hcont.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht ↦ ⟨hp.1, ht⟩)
    have hn : J ∩ (fun t ↦ α (p.1, t)) ⁻¹' A ∈ nhds r :=
      inter_mem (hJ.mem_nhds hr)
        ((hγc.continuousAt (hJ.mem_nhds hr)).preimage_mem_nhds (hA.mem_nhds hqA))
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hn
    let a := min ε (δ / 3)
    have ha : 0 < a := lt_min hε (by positivity)
    have haε : a ≤ ε := min_le_left ..
    have haδ : a ≤ δ / 3 := min_le_right ..
    have hnear {s : ℝ} (hs : s ∈ Ioo (r - a) (r + a)) :
        s ∈ J ∧ α (p.1, s) ∈ A := by
      apply hεsub
      rw [Metric.mem_ball, Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    refine ⟨Ioo (r - a) (r + a), isOpen_Ioo, ⟨by linarith, by linarith⟩,
      fun s hs ↦ (hnear hs).1, ?_⟩
    intro s hs t ht hsC
    obtain ⟨W, hW, hpW, hWU, G, hG, heq⟩ := hsC
    let W' := W ∩ G ⁻¹' A
    have hW' : IsOpen W' := hG.continuousOn.isOpen_inter_preimage hW hA
    have hdt : t - s ∈ Ioo (-δ) δ := by
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
    refine ⟨W', hW', ⟨hpW, ?_⟩, inter_subset_left.trans hWU,
      fun w ↦ Ψ (G w, t - s), ?_, ?_⟩
    · change G p.1 ∈ A
      rw [heq hpW]
      exact (hnear hs).2
    · exact hΨ.comp ((hG.mono inter_subset_left).prodMk contDiffOn_const)
        (fun w hw ↦ ⟨hw.2, hdt⟩)
    · intro w hw
      change Ψ (G w, t - s) = α (w, t)
      rw [heq hw.1]
      exact restart_eq hΩ hF hcJ hα hαΩ hδ hΨzero hΨcurve hΨΩ
        (hWU hw.1) (hnear hs).1 (hnear ht).1 (by have hh := hw.2; change G w ∈ A at hh; rwa [heq hw.1] at hh) hdt
  have hCopen : IsOpen (C ∩ J) := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    obtain ⟨O, hO, hsO, hOJ, hprop⟩ := htransfer s hs.2
    exact mem_of_superset (hO.mem_nhds hsO) (fun t ht ↦ ⟨hprop s hsO t ht hs.1, hOJ ht⟩)
  have hclosed : closure (C ∩ J) ∩ J ⊆ C ∩ J := by
    intro r hr
    obtain ⟨O, hO, hrO, hOJ, hprop⟩ := htransfer r hr.2
    obtain ⟨s, hsO, hsC⟩ := mem_closure_iff_nhds.mp hr.1 O (hO.mem_nhds hrO)
    exact ⟨hprop s hsO r hrO hsC.1, hr.2⟩
  have hstart : 0 ∈ C :=
    ⟨U, hU, hp.1, Subset.rfl, fun w ↦ α (w, 0), hzero, fun _ _ ↦ rfl⟩
  have htC := (hcJ.isPreconnected.subset_of_closure_inter_subset hCopen
    ⟨0, h0, hstart, h0⟩ hclosed hp.2).1
  obtain ⟨W, hW, hpW, hWU, G, hG, heq⟩ := htC
  obtain ⟨A, δ, Ψ, hA, hqA, hδ, hΨ, hΨzero, hΨcurve, hΨΩ⟩ :=
    hlocal (α p) (hαΩ p.1 hp.1 p.2 hp.2)
  let W' := W ∩ G ⁻¹' A
  have hW' : IsOpen W' := hG.continuousOn.isOpen_inter_preimage hW hA
  have hpW' : p.1 ∈ W' := ⟨hpW, by change G p.1 ∈ A; rw [heq hpW]; exact hqA⟩
  let L := J ∩ Ioo (p.2 - δ) (p.2 + δ)
  have hL : IsOpen L := hJ.inter isOpen_Ioo
  have hpL : p.2 ∈ L := ⟨hp.2, by constructor <;> linarith⟩
  let ξ : P × ℝ → E := fun z ↦ Ψ (G z.1, z.2 - p.2)
  have hξ : ContDiffOn ℝ n ξ (W' ×ˢ L) := by
    exact hΨ.comp
      (((hG.mono inter_subset_left).comp contDiffOn_fst (fun _ hz ↦ hz.1)).prodMk
        (contDiffOn_snd.sub contDiffOn_const))
      (fun z hz ↦ ⟨hz.1.2, by constructor <;> linarith [hz.2.2.1, hz.2.2.2]⟩)
  apply ContDiffAt.contDiffWithinAt
  apply (hξ.contDiffAt ((hW'.prod hL).mem_nhds ⟨hpW', hpL⟩)).congr_of_eventuallyEq
  filter_upwards [(hW'.prod hL).mem_nhds ⟨hpW', hpL⟩] with z hz
  change α z = Ψ (G z.1, z.2 - p.2)
  rw [heq hz.1.1]
  exact (restart_eq hΩ hF hcJ hα hαΩ hδ hΨzero hΨcurve hΨΩ
    (hWU hz.1.1) hp.2 hz.2.1 (by have hh := hz.1.2; change G z.1 ∈ A at hh; rwa [heq hz.1.1] at hh)
    (by constructor <;> linarith [hz.2.2.1, hz.2.2.2])).symm

end HolomorphicAnosov.W07FiniteFlowContinuation
