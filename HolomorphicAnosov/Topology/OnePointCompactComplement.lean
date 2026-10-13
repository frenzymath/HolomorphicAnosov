import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Compact plane complements in the one-point compactification

This file compares components of a compact planar complement with those in the sphere.
-/

open Set
open scoped Topology _root_.Topology
namespace HolomorphicAnosov.Topology

/-- For a compact planar set, passing to the one-point compactification does not merge distinct complementary components. (Conway, Ch. 13 §1; Lemma 5.4) -/
theorem onePoint_complex_complement_component {K : Set ℂ} (hK : IsCompact K)
    {x y : ℂ} (hx : x ∉ K) (hy : y ∉ K)
    (hxy : (y : OnePoint ℂ) ∈ connectedComponentIn
      (((↑) : ℂ → OnePoint ℂ) '' K)ᶜ (x : OnePoint ℂ)) :
    y ∈ connectedComponentIn Kᶜ x := by
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.subset_closedBall_lt 0 0
  let E : Set ℂ := {z | r < ‖z‖}
  have hE : IsPreconnected E := by
    have hdim : 1 < Module.rank ℝ ℂ := by
      rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
      norm_num
    have hs := (isPreconnected_sphere hdim (0 : ℂ) 1).prod
      (isPreconnected_Ioi (a := r))
    have himg : (fun p : ℂ × ℝ ↦ p.2 • p.1) ''
        (Metric.sphere (0 : ℂ) 1 ×ˢ Ioi r) = E := by
      ext z
      constructor
      · rintro ⟨⟨w, t⟩, ⟨hw, ht⟩, rfl⟩
        have hw' : ‖w‖ = 1 := by simpa using hw
        simpa [E, norm_smul, Real.norm_eq_abs, abs_of_pos (hr.trans ht), hw'] using ht
      · intro hz
        have hn : 0 < ‖z‖ := hr.trans hz
        refine ⟨⟨‖z‖⁻¹ • z, ‖z‖⟩, ⟨?_, hz⟩, ?_⟩
        · simp [hn.ne']
        · simp [hn.ne']
    rw [← himg]
    exact hs.image _ (continuous_snd.smul continuous_fst).continuousOn
  have hEK : E ⊆ Kᶜ := by
    intro z hz hzK
    have := hKr hzK
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    exact (not_lt_of_ge this) hz
  have hU : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  let C := fun z : ℂ ↦ connectedComponentIn Kᶜ z
  have hCopen (z : ℂ) : IsOpen (C z) := hU.connectedComponentIn
  have hCclosed (z : ℂ) : IsClosed (C z ∪ K) := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro w hw
    have hwK : w ∈ Kᶜ := fun h ↦ hw (Or.inr h)
    have hwC : w ∉ C z := fun h ↦ hw (Or.inl h)
    apply Filter.mem_of_superset ((hCopen w).mem_nhds (mem_connectedComponentIn hwK))
    intro v hv hvc
    rcases hvc with hvC | hvK
    · apply hwC
      have heq := (connectedComponentIn_eq hv).trans (connectedComponentIn_eq hvC).symm
      change w ∈ connectedComponentIn Kᶜ z
      rw [← heq]
      exact mem_connectedComponentIn hwK
    · exact (connectedComponentIn_subset Kᶜ w hv) hvK
  have hbounded (z : ℂ) (hz : z ∉ K) (hdis : Disjoint (C z) E) :
      connectedComponentIn (((↑) : ℂ → OnePoint ℂ) '' K)ᶜ (z : OnePoint ℂ) ⊆
        ((↑) : ℂ → OnePoint ℂ) '' C z := by
    have hsub : C z ∪ K ⊆ Metric.closedBall 0 r := by
      intro w hw
      rcases hw with hw | hw
      · simp only [Metric.mem_closedBall, dist_zero_right]
        exact le_of_not_gt (fun h ↦ Set.disjoint_left.mp hdis hw h)
      · exact hKr hw
    have hcompact : IsCompact (C z ∪ K) :=
      (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset (hCclosed z) hsub
    have hclosed : IsClosed (((↑) : ℂ → OnePoint ℂ) '' (C z ∪ K)) :=
      hcompact.image OnePoint.continuous_coe |>.isClosed
    apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
      (OnePoint.isOpen_image_coe.mpr (hCopen z))
    · refine ⟨(z : OnePoint ℂ), mem_connectedComponentIn ?_,
        ⟨z, mem_connectedComponentIn hz, rfl⟩⟩
      simpa using hz
    · rintro w ⟨hwcl, hwcomp⟩
      have hw := (closure_minimal (image_mono subset_union_left) hclosed) hwcl
      rcases hw with ⟨v, hv, rfl⟩
      rcases hv with hv | hv
      · exact ⟨v, hv, rfl⟩
      · exact False.elim ((connectedComponentIn_subset _ _ hwcomp) ⟨v, hv, rfl⟩)
  by_cases hCx : Disjoint (C x) E
  · have := hbounded x hx hCx hxy
    simpa using this
  by_cases hCy : Disjoint (C y) E
  · have hyx : (x : OnePoint ℂ) ∈ connectedComponentIn
        (((↑) : ℂ → OnePoint ℂ) '' K)ᶜ (y : OnePoint ℂ) := by
      rw [← connectedComponentIn_eq hxy]
      exact mem_connectedComponentIn (by simpa using hx)
    have hxCy : x ∈ C y := by simpa using hbounded y hy hCy hyx
    rw [← connectedComponentIn_eq hxCy]
    exact mem_connectedComponentIn hy
  · obtain ⟨u, huC, huE⟩ := Set.not_disjoint_iff.mp hCx
    obtain ⟨v, hvC, hvE⟩ := Set.not_disjoint_iff.mp hCy
    have hvCu : v ∈ connectedComponentIn Kᶜ u :=
      hE.subset_connectedComponentIn huE hEK hvE
    have heq : C x = C y := (connectedComponentIn_eq huC).trans
      ((connectedComponentIn_eq hvCu).trans (connectedComponentIn_eq hvC).symm)
    change y ∈ C x
    rw [heq]
    exact mem_connectedComponentIn hy
end HolomorphicAnosov.Topology
