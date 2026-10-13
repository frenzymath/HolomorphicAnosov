import HolomorphicAnosov.Paper.Zhang.StableFoliations
import Mathlib.Topology.LocallyConstant.Basic


/-!
# Asymptotic labels on connected native plaques

This file records that a locally constant asymptotic label is constant along a connected plaque. (HPS, §7; Ghys, §5)
-/

noncomputable section
open Set Filter Topology _root_.Topology
namespace HolomorphicAnosov

universe u v

theorem connected_native_plaque_asymptotic_g5
    {I M : Type*} [TopologicalSpace I] [PreconnectedSpace I]
    [MetricSpace M] (f : M ≃ₜ M) (h : I → M)
    (hlift : ∀ t, ∃ V : Set I, IsOpen V ∧ t ∈ V ∧
      ∃ ψ : V → StableAsymptoticLeaf f (h t),
        ∀ s : V, (ψ s).val = h s.val)
    (s t : I) : ForwardAsymptotic f (h s) (h t) := by
  have heqv : Equivalence (ForwardAsymptotic f) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      simp [ForwardAsymptotic]
    · intro x y hxy
      simpa only [ForwardAsymptotic, dist_comm] using hxy
    · intro x y z hxy hyz
      apply squeeze_zero (fun _ ↦ dist_nonneg)
        (fun n ↦ dist_triangle ((f : M → M)^[n] z)
          ((f : M → M)^[n] y) ((f : M → M)^[n] x))
      simpa only [add_zero] using hyz.add hxy
  let R : Setoid I :=
    { r := fun a b ↦ ForwardAsymptotic f (h a) (h b)
      iseqv := ⟨fun a ↦ heqv.refl (h a),
        fun hab ↦ heqv.symm hab,
        fun hab hbc ↦ heqv.trans hab hbc⟩ }
  have hlocal : IsLocallyConstant (Quotient.mk R) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro a
    obtain ⟨V, hV, haV, ψ, hψ⟩ := hlift a
    filter_upwards [hV.mem_nhds haV] with b hb
    apply Quotient.sound
    exact R.symm (by
      have hm := (ψ ⟨b, hb⟩).property
      have hm' : ForwardAsymptotic f (h a) (h b) := by
        simpa only [hψ ⟨b, hb⟩] using hm
      exact hm')
  have hquot := hlocal.apply_eq_of_preconnectedSpace s t
  change ForwardAsymptotic f (h s) (h t)
  exact Quotient.exact hquot


end HolomorphicAnosov
