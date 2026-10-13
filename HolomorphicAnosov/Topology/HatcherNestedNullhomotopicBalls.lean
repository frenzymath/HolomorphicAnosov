import HolomorphicAnosov.Topology.HatcherCenteredNullhomotopicBall
import Mathlib.Tactic.Linarith

namespace HolomorphicAnosov

/-- Quantitative nested centered balls for Hatcher's skeletal induction.

Source: Hatcher, Algebraic Topology, Theorem A.7, p.526, the nested balls
`U_n ⊃ V_n ⊃ … ⊃ U_0 ⊃ V_0`. We index from the outside inward.
Choose a nullhomotopic inner ball in the prescribed outer ball, then take the
next outer radius to be one tenth of that inner radius and repeat. The next
inner radius is smaller still, so its radius plus four times its outer radius
is strictly smaller than the preceding inner radius. Reversing any finite
initial segment gives the sequence used in the finite-dimensional induction.
No compactness or dimension assumption is needed for this neighborhood choice. -/
theorem hatcher_nested_nullhomotopic_balls
    {X : Type*} [PseudoMetricSpace X]
    (C : Set X)
    (hlocal : ∀ (c : C) (O : Set C), IsOpen O → c ∈ O →
      ∃ V : Set C, IsOpen V ∧ c ∈ V ∧
        ∃ hVO : V ⊆ O, (ContinuousMap.inclusion hVO).Nullhomotopic)
    (c : C) (ε : ℝ) (hε : 0 < ε) :
    ∃ r R : ℕ → ℝ, R 0 = ε ∧
      (∀ n, 0 < r n ∧ r n < R n ∧
        ∃ hsub : Metric.ball c (r n) ⊆ Metric.ball c (R n),
          (ContinuousMap.inclusion hsub).Nullhomotopic) ∧
      ∀ n, r (n + 1) + 4 * R (n + 1) < r n := by
  classical
  let P := {t : ℝ // 0 < t}
  have hchoose (t : P) := hatcher_centered_nullhomotopic_ball C hlocal c t.val t.property
  let inner : P → ℝ := fun t ↦ (hchoose t).choose
  have hi (t : P) : 0 < inner t ∧ inner t < t.val ∧
      ∃ hsub : Metric.ball c (inner t) ⊆ Metric.ball c t.val,
        (ContinuousMap.inclusion hsub).Nullhomotopic := (hchoose t).choose_spec
  let next : P → P := fun t ↦ ⟨inner t / 10, div_pos (hi t).1 (by norm_num)⟩
  let outer : ℕ → P := fun n ↦ Nat.rec ⟨ε, hε⟩ (fun _ t ↦ next t) n
  refine ⟨fun n ↦ inner (outer n), fun n ↦ (outer n).val, rfl, ?_, ?_⟩
  · exact fun n ↦ hi (outer n)
  · intro n
    have hn := (hi (outer (n + 1))).2.1
    have hp := (hi (outer n)).1
    change inner (outer (n + 1)) < inner (outer n) / 10 at hn
    change inner (outer (n + 1)) + 4 * (inner (outer n) / 10) < inner (outer n)
    linarith


end HolomorphicAnosov
