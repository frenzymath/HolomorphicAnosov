import Mathlib.Topology.ContinuousMap.ZeroAtInfty

open Filter _root_.Topology
open scoped ZeroAtInfty BoundedContinuousFunction

namespace HolomorphicAnosov.Analysis

/-- A function continuous on a ball has bounded values along each null sequence in that ball.
Source: Wells (1976), p.288, finite-head/tail argument. Its values converge to `f 0`
and hence form a bounded sequence. This construction retains the constant tail value;
it is used for derivative coefficients, which need not vanish at zero. -/
theorem c0_bounded_composition_exists
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (s : ℝ) (hs : 0 < s) (f : E → F)
    (hf : ContinuousOn f (Metric.ball 0 s)) :
    ∃ B : C₀(ℕ, E) → (ℕ →ᵇ F),
      ∀ w ∈ Metric.ball (0 : C₀(ℕ, E)) s, ∀ n, B w n = f (w n) := by
  classical
  have hf0 : ContinuousAt f 0 := (hf 0 (by simpa using hs)).continuousAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hs))
  have hbounded (w : C₀(ℕ, E)) : Bornology.IsBounded (Set.range (fun n ↦ f (w n))) := by
    apply Metric.isBounded_range_of_tendsto (x := f 0)
    exact hf0.tendsto.comp (by simpa [cocompact_eq_atTop] using zero_at_infty w)
  choose R hR using fun w : C₀(ℕ, E) ↦ (hbounded w).exists_norm_le
  exact ⟨fun w ↦ BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n ↦ f (w n)) (R w) (fun n ↦ hR w _ (Set.mem_range_self n)), fun _ _ _ ↦ rfl⟩

end HolomorphicAnosov.Analysis

