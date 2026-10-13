import Mathlib.Topology.Algebra.OpenSubgroup
import HolomorphicAnosov.Dynamics.AsymptoticLeaf
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.UniformSpace.HeineCantor

open scoped Topology _root_.Topology
open Filter Set

namespace HolomorphicAnosov

noncomputable section

/-- Compact uniform continuity compares the original base asymptotic relation with the quotient
linear orbit of a difference of representatives. -/
theorem asymptotic_quotient_iff
    {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace M] [CompactSpace M]
    (Γ : Submodule ℤ V) [DiscreteTopology Γ]
    (A : V ≃L[ℝ] V) (f : M ≃ₜ M) (h : M ≃ₜ V ⧸ Γ.toAddSubgroup)
    (hc : ∀ x v, (QuotientAddGroup.mk v : V ⧸ Γ.toAddSubgroup) = h x →
      h (f x) = (QuotientAddGroup.mk (A v) : V ⧸ Γ.toAddSubgroup))
    (x z : M) (vx vz : V)
    (hx : (QuotientAddGroup.mk vx : V ⧸ Γ.toAddSubgroup) = h x)
    (hz : (QuotientAddGroup.mk vz : V ⧸ Γ.toAddSubgroup) = h z) :
    ForwardAsymptotic f x z ↔
      Tendsto (fun n : ℕ ↦ (QuotientAddGroup.mk ((A : V → V)^[n] (vz - vx)) :
        V ⧸ Γ.toAddSubgroup)) atTop (𝓝 0) := by
  let : IsClosed (Γ.toAddSubgroup : Set V) := AddSubgroup.isClosed_of_discreteTopology
  let : CompactSpace (V ⧸ Γ.toAddSubgroup) := h.compactSpace
  have hi : ∀ (n : ℕ) (w : M) (v : V),
      (QuotientAddGroup.mk v : V ⧸ Γ.toAddSubgroup) = h w →
      h ((f : M → M)^[n] w) = QuotientAddGroup.mk ((A : V → V)^[n] v) := by
    intro n
    induction n with
    | zero => intro w v hv; exact hv.symm
    | succ n ih =>
      intro w v hv
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hc _ _ (ih w v hv).symm
  have hsub : ∀ n : ℕ, (A : V → V)^[n] (vz - vx) =
      (A : V → V)^[n] vz - (A : V → V)^[n] vx := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', ih, map_sub]
  have hd : ∀ n : ℕ, ‖(QuotientAddGroup.mk ((A : V → V)^[n] (vz - vx)) :
      V ⧸ Γ.toAddSubgroup)‖ =
      dist (h ((f : M → M)^[n] z)) (h ((f : M → M)^[n] x)) := by
    intro n
    rw [hi n x vx hx, hi n z vz hz, dist_eq_norm, hsub]
    exact congrArg norm ((QuotientAddGroup.mk' Γ.toAddSubgroup).map_sub _ _)
  have hquot : Tendsto (fun n : ℕ ↦ (QuotientAddGroup.mk ((A : V → V)^[n] (vz - vx)) :
      V ⧸ Γ.toAddSubgroup)) atTop (𝓝 0) ↔
      Tendsto (fun n : ℕ ↦ dist (h ((f : M → M)^[n] z))
        (h ((f : M → M)^[n] x))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [hd]
  rw [ForwardAsymptotic, hquot]
  constructor
  · intro ht
    have hh : Tendsto (fun w : M × M ↦ (h w.1, h w.2)) (uniformity M)
        (uniformity (V ⧸ Γ.toAddSubgroup)) :=
      CompactSpace.uniformContinuous_of_continuous h.continuous
    have hs : Tendsto (fun n : ℕ ↦ ((f : M → M)^[n] z, (f : M → M)^[n] x))
        atTop (uniformity M) := tendsto_uniformity_iff_dist_tendsto_zero.mpr ht
    exact tendsto_uniformity_iff_dist_tendsto_zero.mp (hh.comp hs)
  · intro ht
    have hh : Tendsto (fun w : (V ⧸ Γ.toAddSubgroup) × (V ⧸ Γ.toAddSubgroup) ↦
        (h.symm w.1, h.symm w.2)) (uniformity (V ⧸ Γ.toAddSubgroup)) (uniformity M) :=
      CompactSpace.uniformContinuous_of_continuous h.symm.continuous
    have hs : Tendsto (fun n : ℕ ↦ (h ((f : M → M)^[n] z), h ((f : M → M)^[n] x)))
        atTop (uniformity (V ⧸ Γ.toAddSubgroup)) := tendsto_uniformity_iff_dist_tendsto_zero.mpr ht
    have hl := tendsto_uniformity_iff_dist_tendsto_zero.mp (hh.comp hs)
    simpa only [Function.comp_apply, h.symm_apply_apply] using hl


end
end HolomorphicAnosov
