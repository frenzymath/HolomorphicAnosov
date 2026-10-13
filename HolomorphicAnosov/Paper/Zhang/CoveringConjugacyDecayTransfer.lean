import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Topology _root_.Topology
open Filter Set

universe u v
namespace HolomorphicAnosov

/-- A linear coordinate change preserves the exact zero-decay condition, because both it and its inverse are continuous and it intertwines every iterate. -/
theorem covering_conjugacy_transfer_decay_g15
    {V : Type u} {W : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃L[ℝ] W) (A : V ≃L[ℝ] V) (B : W ≃L[ℝ] W)
    (hconj : ∀ v, e (A v) = B (e v)) (v : V) :
    Tendsto (fun n : ℕ ↦ A^[n] v) atTop (𝓝 0) ↔
      Tendsto (fun n : ℕ ↦ B^[n] (e v)) atTop (𝓝 0) := by
  have hn : ∀ n : ℕ, e (A^[n] v) = B^[n] (e v) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', hconj, ih]
  constructor
  · intro hv
    simpa only [Function.comp_def, hn, map_zero] using (e.continuous.tendsto 0).comp hv
  · intro hv
    have hn' n : e.symm (B^[n] (e v)) = A^[n] v := by rw [← hn, e.symm_apply_apply]
    simpa only [Function.comp_def, hn', map_zero] using (e.symm.continuous.tendsto 0).comp hv


end HolomorphicAnosov
