import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

noncomputable section
open Filter _root_.Topology
namespace HolomorphicAnosov

/-- HPS, *Invariant Manifolds*, pp.32–33, bounded-forcing preparation for
regularity of an invariant section. Let P be a bounded section over a metric
space with return map R of Lipschitz constant c. Suppose its fixed-section
comparison is `dist(P x,P y) ≤ q dist(P(R x),P(R y)) + L dist(x,y)`, with
`q<1` and `qc<1`. Then P is Lipschitz with constant `L/(1-qc)`.

Proof: put K=L/(1-qc), so L+qcK=K. Induction gives the estimate
`dist(P x,P y) ≤ 2M q^n + K dist(x,y)`, where M bounds the distance of P
from a fixed origin. The base case is the triangle inequality and the step
uses the return bound and the identity for K. Let n tend to infinity;
q^n tends to zero. No differentiability of P is used, and q=0 or c=0 is
allowed. This is the source preparation preceding differentiation of P. -/
theorem parameter_graph_bounded_forcing
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (R : X → X) (P : X → Y) (y₀ : Y) (q c L : NNReal) (M : ℝ)
    (hq : (q : ℝ) < 1) (hqc : (q : ℝ) * c < 1)
    (hR : LipschitzWith c R) (hP : ∀ x, dist (P x) y₀ ≤ M)
    (hstep : ∀ x y, dist (P x) (P y) ≤
      (q : ℝ) * dist (P (R x)) (P (R y)) + (L : ℝ) * dist x y) :
    ∀ x y, dist (P x) (P y) ≤ (L : ℝ) / (1 - (q : ℝ) * c) * dist x y := by
  let K : ℝ := (L : ℝ) / (1 - (q : ℝ) * c)
  have hK : 0 ≤ K := div_nonneg L.2 (sub_pos.mpr hqc).le
  have hKeq : (q : ℝ) * c * K + L = K := by
    dsimp [K]
    field_simp [ne_of_gt (sub_pos.mpr hqc)]
    ring
  have hi : ∀ n : ℕ, ∀ x y, dist (P x) (P y) ≤
      2 * M * (q : ℝ) ^ n + K * dist x y := by
    intro n
    induction n with
    | zero =>
      intro x y
      have hb : dist (P x) (P y) ≤ 2 * M := calc
        _ ≤ dist (P x) y₀ + dist y₀ (P y) := dist_triangle _ _ _
        _ ≤ M + M := add_le_add (hP x) (by simpa only [dist_comm] using hP y)
        _ = _ := by ring
      simpa only [pow_zero, mul_one] using
        hb.trans (le_add_of_nonneg_right (mul_nonneg hK dist_nonneg))
    | succ n ih =>
      intro x y
      calc
        _ ≤ (q : ℝ) * dist (P (R x)) (P (R y)) + (L : ℝ) * dist x y := hstep x y
        _ ≤ (q : ℝ) * (2 * M * (q : ℝ) ^ n + K * dist (R x) (R y)) +
            (L : ℝ) * dist x y := add_le_add
              (mul_le_mul_of_nonneg_left (ih _ _) q.2) le_rfl
        _ ≤ (q : ℝ) * (2 * M * (q : ℝ) ^ n + K * ((c : ℝ) * dist x y)) +
            (L : ℝ) * dist x y := by
          gcongr
          exact hR.dist_le_mul x y
        _ = 2 * M * (q : ℝ) ^ (n+1) + ((q : ℝ) * c * K + L) * dist x y := by
          rw [pow_succ]
          ring
        _ = _ := by rw [hKeq]
  intro x y
  have hlim : Tendsto (fun n : ℕ ↦ 2 * M * (q : ℝ)^n + K * dist x y)
      atTop (𝓝 (K * dist x y)) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one q.2 hq).const_mul (2*M)).add_const
      (K * dist x y)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall (fun n ↦ hi n x y))

end HolomorphicAnosov
