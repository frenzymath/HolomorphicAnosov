import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.Basic

open scoped Topology _root_.Topology
open Filter Set

namespace HolomorphicAnosov

noncomputable section

/-- Discreteness and injectivity exclude a nonzero lattice vector with decaying iterates. -/
theorem lattice_decay_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Γ : Submodule ℤ V) [DiscreteTopology Γ]
    (A : V ≃L[ℝ] V) (hΓ : A '' (Γ : Set V) = (Γ : Set V))
    (v : V) (hmem : v ∈ Γ)
    (hv : Tendsto (fun n : ℕ ↦ (A : V → V)^[n] v) atTop (𝓝 0)) : v = 0 := by
  have hAmem : ∀ w ∈ Γ, A w ∈ Γ := by
    intro w hw
    change A w ∈ (Γ : Set V)
    rw [← hΓ]
    exact ⟨w, hw, rfl⟩
  have hi : ∀ k : ℕ, (A : V → V)^[k] v ∈ Γ := by
    intro k
    induction k with
    | zero => exact hmem
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hAmem _ ih
  let seq : ℕ → Γ := fun n ↦ ⟨(A : V → V)^[n] v, hi n⟩
  have hs : Tendsto seq atTop (𝓝 (0 : Γ)) := tendsto_subtype_rng.mpr hv
  have he : ∀ᶠ n in atTop, seq n = 0 := by
    apply tendsto_pure.mp
    simpa only [nhds_discrete] using hs
  obtain ⟨n, hn⟩ := he.exists
  have hz : (A : V → V)^[n] v = 0 := congrArg Subtype.val hn
  have hinj : Function.Injective ((A : V → V)^[n]) := A.injective.iterate n
  apply hinj
  rw [hz]
  exact Function.Semiconj.iterate_right
    (show Function.Semiconj (fun _ : Unit ↦ (0 : V)) id A from
      fun _ ↦ (map_zero A).symm) n ()


end
end HolomorphicAnosov
