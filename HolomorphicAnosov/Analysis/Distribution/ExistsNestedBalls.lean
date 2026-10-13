import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Tactic

open TopologicalSpace

namespace HolomorphicAnosov

open Set
open scoped Topology _root_.Topology

/-! A geometric fragment of Step 1 in the source proof.  The open-set
metric-ball characterization gives a ball around the chosen point; shrinking
its radius by a fixed factor places the required closed four-radius ball
inside that same open set.  The returned `V` is the inner open ball used by
the local representation, while the closed-ball inclusion is the margin for
the cutoff support.  This helper changes no public statement and adds no
geometric assumption. -/
theorem exists_nested_balls {n : ℕ} (U : Opens (Fin n → ℂ))
    {a : Fin n → ℂ} (ha : a ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∃ V : Opens (Fin n → ℂ),
      a ∈ V ∧ V ≤ U ∧
        Metric.closedBall a (4 * r) ⊆ (U : Set (Fin n → ℂ)) := by
  rcases (Metric.isOpen_iff.mp U.isOpen a ha) with ⟨ε, hε, hsub⟩
  refine ⟨ε / 8, by positivity, ⟨⟨Metric.ball a (ε / 8), Metric.isOpen_ball⟩, ?_, ?_, ?_⟩⟩
  · exact Metric.mem_ball.mpr (by simpa [dist_self] using
      (show (0 : ℝ) < ε / 8 by positivity))
  · intro x hx
    exact hsub (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hx)
      (by linarith [hε])))
  · have hcalc : 4 * (ε / 8) < ε := by nlinarith [hε]
    exact (Metric.closedBall_subset_ball hcalc).trans hsub


end HolomorphicAnosov
