import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Sequences

/-!
# Closedness of continuous evaluation for bounded dependent complex covectors

The fibre norms and total-space topology are the supplied ones. The only
compatibility assumption is continuity of the fibre norm on that total space.
This supplies the uniform-limit continuity step omitted from the complete section
metric assertion of Ghys, *Holomorphic Anosov systems*, pp.591–592. The argument
below is an agent-written deduction from the operator-norm estimate and Mathlib's
locally uniform limit theorem. No compactness, bundle
trivialization, nonempty base, or finite-dimensionality is needed for this step.
-/

open Set Bundle Filter
open scoped Topology _root_.Topology ENNReal
noncomputable section

namespace HolomorphicAnosov

/-- Bounded complex covector fields with continuous evaluation form a closed
subset of the dependent supremum-norm space.

Proof: let covector fields `bₙ` converge in the dependent supremum norm to `b`.
At any total-space vector `v`, continuity of the supplied fibre norm gives a
neighborhood on which the norm is less than `‖v‖ + 1`. The operator-norm
inequality bounds the evaluation difference there by
`‖b - bₙ‖ * (‖v‖ + 1)`. This tends to zero uniformly on that neighborhood.
Thus the evaluations converge locally uniformly in the original topology.
Every approximating evaluation is continuous, so the limit is continuous.
Sequential closedness is closedness because the dependent `lp` space is metric.

Origin: agent-written detail for `ghys.homogeneous_jet_section_metric`, filling
the continuity step in Ghys pp.591–592. Inputs: the bounded-operator estimate
of Rudin, *Real and Complex Analysis*, Definition 5.3, p.96; Mathlib
`TendstoLocallyUniformly.continuous` and `IsSeqClosed.isClosed`.
DAG node: `analysis.continuous_dual_evaluation_closed_g1`.
-/
theorem continuous_dual_evaluation_closed
    {B : Type*} {E : B → Type*}
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
    [TopologicalSpace (TotalSpace ℂ E)]
    (hnorm : Continuous (fun v : TotalSpace ℂ E ↦ ‖v.snd‖)) :
    IsClosed {b : lp (fun x : B ↦ E x →L[ℂ] ℂ) ∞ |
      Continuous (fun v : TotalSpace ℂ E ↦ b v.proj v.snd)} := by
  apply IsSeqClosed.isClosed
  intro b limit hb hlim
  have hlocal : TendstoLocallyUniformly
      (fun n (v : TotalSpace ℂ E) ↦ b n v.proj v.snd)
      (fun v : TotalSpace ℂ E ↦ limit v.proj v.snd) atTop := by
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hε v
    let C := ‖v.snd‖ + 1
    have hC : 0 < C := by dsimp [C]; positivity
    refine ⟨{w : TotalSpace ℂ E | ‖w.snd‖ < C}, ?_, ?_⟩
    · exact hnorm.continuousAt.preimage_mem_nhds
        (Iio_mem_nhds (by dsimp [C]; linarith))
    · have hsmall : ∀ᶠ n in atTop, dist (b n) limit < ε / C :=
        (Metric.tendsto_atTop.1 hlim) (ε / C) (div_pos hε hC) |>.elim
          (fun N hN ↦ eventually_atTop.2 ⟨N, hN⟩)
      filter_upwards [hsmall] with n hn
      intro w hw
      rw [dist_eq_norm]
      have hn' : ‖limit - b n‖ < ε / C := by
        simpa only [dist_eq_norm, norm_sub_rev] using hn
      calc
        ‖limit w.proj w.snd - b n w.proj w.snd‖ ≤
            ‖(limit - b n) w.proj‖ * ‖w.snd‖ :=
          ((limit - b n) w.proj).le_opNorm w.snd
        _ ≤ ‖limit - b n‖ * ‖w.snd‖ :=
          mul_le_mul_of_nonneg_right
            (lp.norm_apply_le_norm ENNReal.top_ne_zero (limit - b n) w.proj)
            (norm_nonneg _)
        _ ≤ ‖limit - b n‖ * C :=
          mul_le_mul_of_nonneg_left hw.le (norm_nonneg _)
        _ < ε := (lt_div_iff₀ hC).mp hn'
  exact hlocal.continuous (Eventually.of_forall hb).frequently


end HolomorphicAnosov
