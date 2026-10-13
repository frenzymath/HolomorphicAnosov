import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.ExtendCertificate
import HolomorphicAnosov.Geometry.SmoothLocalFlow
import Mathlib.Topology.Connected.Basic

/-! Integral curves of smooth vector fields admit smooth endpoint maps near their initial points. -/

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.W07FlowContinuation

open Set Filter
open scoped Manifold ContDiff Topology _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [BoundarylessManifold I N] [T2Space N]
  {V : (x : N) → TangentSpace I x}

/-- At each time of a smooth integral curve, a smooth map on a neighborhood of its initial point
gives the endpoints of integral curves from nearby initial points. -/
theorem endpoint_certificate
    [FiniteDimensional ℝ E]
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I N)))
    {J : Set ℝ} (hJ : IsOpen J) (hconn : OrdConnected J) (h0 : 0 ∈ J)
    {γ : ℝ → N} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ J)
    (hcγ : IsMIntegralCurveOn γ V J) {t : ℝ} (ht : t ∈ J) :
    ∃ W, IsOpen W ∧ γ 0 ∈ W ∧ ∃ F : N → N,
      ContMDiffOn I I ∞ F W ∧ F (γ 0) = γ t ∧
      ∀ w ∈ W, ∃ (a b : ℝ) (c : ℝ → N), 0 ∈ Ioo a b ∧ t ∈ Ioo a b ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I ∞ c (Ioo a b) ∧
        IsMIntegralCurveOn c V (Ioo a b) ∧ c 0 = w ∧ c t = F w := by
  classical
  let C : Set ℝ := {s | ∃ W, IsOpen W ∧ γ 0 ∈ W ∧ ∃ F : N → N,
    ContMDiffOn I I ∞ F W ∧ F (γ 0) = γ s ∧ ∀ w ∈ W, Endpoint V s w (F w)}
  have hlocal (r : ℝ) (hr : r ∈ J) :
      ∃ O, IsOpen O ∧ r ∈ O ∧ O ⊆ J ∧
        ∀ s ∈ O, ∀ u ∈ O, s ∈ C → u ∈ C := by
    obtain ⟨U, δ, Ψ, hU, hrU, hδ, hΨ, hzero, hcurve, huniq, hgroup, hdiff⟩ :=
      exists_smoothLocalFlow I V hV (γ r)
    have hneigh : J ∩ γ ⁻¹' U ∈ nhds r :=
      Filter.inter_mem (hJ.mem_nhds hr)
        ((hγ.continuousOn.continuousAt (hJ.mem_nhds hr)).preimage_mem_nhds
          (hU.mem_nhds hrU))
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hneigh
    let a := min ε (δ / 3)
    have ha : 0 < a := lt_min hε (by positivity)
    have haε : a ≤ ε := min_le_left ..
    have haδ : a ≤ δ / 3 := min_le_right ..
    have hball (s : ℝ) (hs : s ∈ Ioo (r - a) (r + a)) : s ∈ Metric.ball r ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    refine ⟨Ioo (r - a) (r + a), isOpen_Ioo, ⟨by linarith, by linarith⟩, ?_, ?_⟩
    · intro s hs
      exact (hεsub (hball s hs)).1
    · intro s hs u hu hsC
      have hsnear : s ∈ J ∩ γ ⁻¹' U := hεsub (hball s hs)
      have hunear : u ∈ J := (hεsub (hball u hu)).1
      have hus : u - s ∈ Ioo (-δ) δ := by
        constructor <;> linarith [hs.1, hs.2, hu.1, hu.2]
      have heq : Ψ (γ s, u - s) = γ u := by
        let D := J ∩ {v : ℝ | v - s ∈ Ioo (-δ) δ}
        have hD : OrdConnected D := hconn.inter (by
          convert (ordConnected_Ioo : OrdConnected (Ioo (s - δ) (s + δ))) using 1
          ext v
          simp only [mem_ofPred_eq, mem_Ioo]
          constructor <;> intro hv <;> constructor <;> linarith [hv.1, hv.2])
        have hshift := (isMIntegralCurveOn_comp_sub (dt := s)).mpr (hcurve (γ s) hsnear.2)
        have hh := huniq D hD s ⟨hsnear.1, by constructor <;> linarith⟩
          (fun v ↦ Ψ (γ s, v - s)) γ
          (hshift.mono inter_subset_right) (hcγ.mono inter_subset_left)
          (by simpa only [sub_self] using hzero (γ s) hsnear.2)
        exact hh ⟨hunear, hus⟩
      have hnew := extend_certificate hV hδ hU hΨ hzero hcurve hsnear.2 hus hsC
      change ∃ W, IsOpen W ∧ γ 0 ∈ W ∧ ∃ F : N → N,
        ContMDiffOn I I ∞ F W ∧ F (γ 0) = γ u ∧ ∀ w ∈ W, Endpoint V u w (F w)
      simpa only [heq] using hnew
  have hCopen : IsOpen (C ∩ J) := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    obtain ⟨O, hO, hsO, hOJ, hprop⟩ := hlocal s hs.2
    apply mem_of_superset (hO.mem_nhds hsO)
    intro u hu
    exact ⟨hprop s hsO u hu hs.1, hOJ hu⟩
  have hclosed : closure (C ∩ J) ∩ J ⊆ C ∩ J := by
    intro r hr
    obtain ⟨O, hO, hrO, hOJ, hprop⟩ := hlocal r hr.2
    obtain ⟨s, hsO, hsC⟩ := mem_closure_iff_nhds.mp hr.1 O (hO.mem_nhds hrO)
    exact ⟨hprop s hsO r hrO hsC.1, hr.2⟩
  have hstart : 0 ∈ C := by
    obtain ⟨U, δ, Ψ, hU, hzU, hδ, hΨ, hzero, hcurve, _, _, _⟩ :=
      exists_smoothLocalFlow I V hV (γ 0)
    refine ⟨U, hU, hzU, id, contMDiffOn_id, rfl, ?_⟩
    intro w hw
    refine ⟨-δ, δ, fun s ↦ Ψ (w, s), ⟨by linarith, hδ⟩,
      ⟨by linarith, hδ⟩, ?_, hcurve w hw, hzero w hw, hzero w hw⟩
    exact hΨ.comp (contMDiffOn_const.prodMk contMDiffOn_id) (fun s hs ↦ ⟨hw, hs⟩)
  exact (hconn.isPreconnected.subset_of_closure_inter_subset hCopen
    ⟨0, h0, hstart, h0⟩ hclosed ht).1

end HolomorphicAnosov.W07FlowContinuation
