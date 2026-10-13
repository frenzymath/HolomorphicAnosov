import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Tactic.Linarith

noncomputable section
namespace HolomorphicAnosov.BoundedLipschitzJets
open Filter Set
open scoped Topology _root_.Topology

/-- Closed annuli are locally finite away from zero, as HPS p.28 uses for pasting.
A neighborhood of a nonzero point has norm bounded below; all sufficiently small
radii lie below that bound, so only finitely many annuli meet this neighborhood. -/
theorem annuli_locallyFinite
    {X : Type*} [NormedAddCommGroup X] {r : ℕ → ℝ}
    (ht : Tendsto r atTop (𝓝 0)) :
    LocallyFinite (fun n ↦ {x : {x : X // x ≠ 0} | r (n+1) ≤ ‖(x : X)‖ ∧ ‖(x : X)‖ ≤ r n}) := by
  intro x
  have hx : 0 < ‖(x : X)‖ / 2 := half_pos (norm_pos_iff.mpr x.property)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 _ hx)
  let U : Set {x : X // x ≠ 0} := {y | ‖(x : X)‖ / 2 < ‖(y : X)‖}
  have hU : U ∈ 𝓝 x :=
    (isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)).mem_nhds (by
      change ‖(x : X)‖ / 2 < ‖(x : X)‖; linarith)
  refine ⟨U, hU, (Set.finite_Iio N).subset ?_⟩
  intro n hn
  obtain ⟨y, hy, hyU⟩ := hn
  change n < N
  by_contra hh
  have hnr := hN n (by omega)
  change ‖(x : X)‖ / 2 < ‖(y : X)‖ at hyU
  linarith [hy.2]

end HolomorphicAnosov.BoundedLipschitzJets

