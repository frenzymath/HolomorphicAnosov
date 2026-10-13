import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

noncomputable section
open Filter _root_.Topology
namespace HolomorphicAnosov

/-- HPS, *Invariant Manifolds*, Theorem 3.1 p.25, with the point-valued
return convention explained on p.58: a bounded fixed section of a continuous
uniform fibre contraction is continuous, even when the return is not invertible.
Start with a constant continuous section and iterate
`Q_(n+1)(x)=Φ(x,Q_n(R(x)))`. The fixed equation and fibre contraction give
`dist(Q_n(x),P(x))≤q^n M` uniformly in x. Since q<1 the iterates converge
uniformly to P. Every iterate is continuous by composition, so P is continuous.
The same estimate is retained as a quantitative convergence conclusion. -/
theorem parameter_graph_point_return_continuity
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    (R : X → X) (hR : Continuous R) (Φ : X → Y → Y)
    (hΦ : Continuous (fun z : X × Y ↦ Φ z.1 z.2))
    (q : NNReal) (hq : (q : ℝ) < 1) (hcontract : ∀ x, LipschitzWith q (Φ x))
    (P : X → Y) (hfix : ∀ x, Φ x (P (R x)) = P x)
    (y₀ : Y) (M : ℝ) (hP : ∀ x, dist y₀ (P x) ≤ M) :
    Continuous P ∧ ∃ Q : ℕ → X → Y,
      Q 0 = (fun _ ↦ y₀) ∧
      (∀ n x, Q (n+1) x = Φ x (Q n (R x))) ∧
      (∀ n, Continuous (Q n)) ∧
      (∀ n x, dist (Q n x) (P x) ≤ (q : ℝ)^n * M) ∧
      TendstoUniformly Q P atTop := by
  let Q : ℕ → X → Y := fun n ↦
    Nat.rec (fun _ ↦ y₀) (fun _ f x ↦ Φ x (f (R x))) n
  have hc : ∀ n, Continuous (Q n) := by
    intro n
    induction n with
    | zero => exact continuous_const
    | succ n ih => exact hΦ.comp (continuous_id.prodMk (ih.comp hR))
  have hb : ∀ n x, dist (Q n x) (P x) ≤ (q : ℝ)^n * M := by
    intro n
    induction n with
    | zero =>
      intro x
      change dist y₀ (P x) ≤ (q : ℝ)^0 * M
      rw [pow_zero,one_mul]
      exact hP x
    | succ n ih =>
      intro x
      change dist (Φ x (Q n (R x))) (P x) ≤ _
      calc
        _ = dist (Φ x (Q n (R x))) (Φ x (P (R x))) := by rw [hfix]
        _ ≤ (q : ℝ) * dist (Q n (R x)) (P (R x)) := (hcontract x).dist_le_mul _ _
        _ ≤ (q : ℝ) * ((q : ℝ)^n * M) := mul_le_mul_of_nonneg_left (ih _) q.2
        _ = _ := by rw [pow_succ']; ring
  have hu : TendstoUniformly Q P atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have hl : Tendsto (fun n : ℕ ↦ (q : ℝ)^n * M) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one q.2 hq).mul_const M
    filter_upwards [hl.eventually_lt_const hε] with n hn x
    simpa only [dist_comm] using (hb n x).trans_lt hn
  refine ⟨hu.continuous (Eventually.of_forall hc).frequently, Q, rfl, fun _ _ ↦ rfl, hc, hb, hu⟩

end HolomorphicAnosov
