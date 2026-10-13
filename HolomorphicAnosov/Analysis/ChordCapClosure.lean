import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Convex.Topology

open Set
open scoped ComplexConjugate

namespace HolomorphicAnosov.Analysis

/-- Every point on the closed side of a chord in the closed unit disk is a limit,
within the closed disk, of points in the strict side and the open disk, provided
that cap has a point. This is the elementary straight-segment step in Tao,
*246C Notes 2* (2018), §2, Theorem 20, final paragraph (local text line 269).
The explicit closure proof is an agent-written expansion of that step.

Join the tested point to the given interior cap point. Positive convex
combinations lie inside the disk, and the affine chord functional is strictly
negative there. The first endpoint lies in the closure of this open segment.
The closed-disk subtype embedding transports that closure to the native subtype.
No distinctness of the chord endpoints is assumed: an interior cap witness
already rules out a zero chord. -/
theorem chordCap_closure (ζ ω : ℂ) (b : Complex.UnitDisc)
    (hb : (conj (ω - ζ) * ((b : ℂ) - ζ)).im < 0)
    (x : Complex.UnitClosedDisc)
    (hx : (conj (ω - ζ) * ((x : ℂ) - ζ)).im ≤ 0) :
    x ∈ closure {w : Complex.UnitClosedDisc |
      (w : ℂ) ∈ Metric.ball (0 : ℂ) 1 ∧
        (conj (ω - ζ) * ((w : ℂ) - ζ)).im < 0} := by
  rw [Complex.UnitClosedDisc.isEmbedding_coe.closure_eq_preimage_closure_image]
  change (x : ℂ) ∈ closure _
  apply closure_mono _ (segment_subset_closure_openSegment
    (left_mem_segment ℝ (x : ℂ) (b : ℂ)))
  apply (openSegment_subset_iff ℝ).mpr
  intro a c ha hc hac
  have hin : a • (x : ℂ) + c • (b : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    have h := (convex_closedBall (0 : ℂ) (1 : ℝ) : Convex ℝ _).combo_self_interior_mem_interior
      x.property (show (b : ℂ) ∈ interior (Metric.closedBall (0 : ℂ) 1) by
        simpa only [interior_closedBall (0 : ℂ) one_ne_zero] using (mem_ball_zero_iff.mpr b.norm_lt_one))
      ha.le hc hac
    rw [← interior_closedBall (0 : ℂ) one_ne_zero]
    exact h
  refine ⟨⟨_, Metric.ball_subset_closedBall hin⟩, ⟨hin, ?_⟩, rfl⟩
  have hlin : (conj (ω - ζ) * (a • (x : ℂ) + c • (b : ℂ) - ζ)).im =
      a * (conj (ω - ζ) * ((x : ℂ) - ζ)).im +
      c * (conj (ω - ζ) * ((b : ℂ) - ζ)).im := by
    have haeq : a = 1 - c := by linarith
    rw [haeq]
    simp only [Complex.real_smul, Complex.mul_im, Complex.mul_re, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  change (conj (ω - ζ) * (a • (x : ℂ) + c • (b : ℂ) - ζ)).im < 0
  rw [hlin]
  exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ha.le hx)
    (mul_neg_of_pos_of_neg hc hb)

end HolomorphicAnosov.Analysis

