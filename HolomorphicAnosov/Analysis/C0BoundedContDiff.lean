import Mathlib.Analysis.Calculus.ContDiff.Basic
import HolomorphicAnosov.Analysis.NullSequenceUniformContinuity
import HolomorphicAnosov.Analysis.C0BoundedComposition
import HolomorphicAnosov.Analysis.C0ToBoundedDiagonal
import HolomorphicAnosov.Analysis.BoundedC0HasFDerivAt

open Filter _root_.Topology
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction

namespace HolomorphicAnosov.Analysis

universe u v

/-- Coordinate superposition from null sequences to bounded sequences preserves finite smoothness.
Source: Wells (1976), p.288, the finite-head/tail induction proving equation (1).
At order zero, continuity at the compact sequence range gives a common coordinate
radius; the supremum norm then proves continuity. For the successor, the derivative
field of `f` induces a bounded coefficient sequence. The induction hypothesis makes
that coefficient map `Cⁿ`, and the bounded bilinear diagonal map makes the derivative
operator field `Cⁿ`. The mean-value remainder gives the actual Fréchet derivative,
so the successor criterion yields `Cⁿ⁺¹`. A universe lift permits induction in which
the codomain changes from `F` to `E →L[ℝ] F`, without restricting the theorem's universes. -/
theorem c0_bounded_contDiffOn
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : ℝ) (hs : 0 < s) (n : ℕ) (f : E → F)
    (hf : ContDiffOn ℝ n f (Metric.ball 0 s))
    (B : C₀(ℕ, E) → (ℕ →ᵇ F))
    (hB : ∀ w ∈ Metric.ball (0 : C₀(ℕ, E)) s, ∀ i, B w i = f (w i)) :
    ContDiffOn ℝ n B (Metric.ball (0 : C₀(ℕ, E)) s) := by
  have hmain
      {E : Type u} {F : Type (max u v)} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F]
      (s : ℝ) (hs : 0 < s) (n : ℕ) (f : E → F)
      (hf : ContDiffOn ℝ n f (Metric.ball 0 s))
      (B : C₀(ℕ, E) → (ℕ →ᵇ F))
      (hB : ∀ w ∈ Metric.ball (0 : C₀(ℕ, E)) s, ∀ i, B w i = f (w i)) :
      ContDiffOn ℝ n B (Metric.ball (0 : C₀(ℕ, E)) s) := by
    induction n generalizing F with
    | zero =>
      rw [Nat.cast_zero, contDiffOn_zero]
      intro w hw
      apply ContinuousAt.continuousWithinAt
      rw [Metric.continuousAt_iff]
      intro ε hε
      have hf0 : ContinuousAt f 0 := (hf.continuousOn 0 (by simpa using hs)).continuousAt
        (Metric.isOpen_ball.mem_nhds (by simpa using hs))
      have hfi (i : ℕ) : ContinuousAt f (w i) := by
        have hi : w i ∈ Metric.ball (0 : E) s := by
          simpa using (BoundedContinuousFunction.norm_coe_le_norm w.toBCF i).trans_lt
            (show ‖w‖ < s by simpa using hw)
        exact (hf.continuousOn _ hi).continuousAt (Metric.isOpen_ball.mem_nhds hi)
      obtain ⟨δ, hδ, hu⟩ := null_sequence_uniform_continuity (fun i ↦ w i)
        (by simpa [cocompact_eq_atTop] using zero_at_infty w) f hf0 hfi (half_pos hε)
      have hw' : ‖w‖ < s := by simpa using hw
      refine ⟨min δ (s - ‖w‖), lt_min hδ (sub_pos.mpr hw'), fun z hz ↦ ?_⟩
      have hzδ : dist z w < δ := hz.trans_le (min_le_left _ _)
      have hzs : ‖z‖ < s := by
        have := hz.trans_le (min_le_right δ (s - ‖w‖))
        have ht := norm_le_norm_add_norm_sub w z
        rw [dist_eq_norm] at this
        rw [norm_sub_rev w z] at ht
        linarith
      have hnorm : dist (B z) (B w) ≤ ε / 2 := by
        apply (BoundedContinuousFunction.dist_le (half_pos hε).le).mpr
        intro i
        rw [hB z (by simpa using hzs), hB w hw]
        exact (hu i (z i) ((BoundedContinuousFunction.dist_coe_le_dist
          (f := z.toBCF) (g := w.toBCF) i).trans_lt hzδ)).le
      exact hnorm.trans_lt (half_lt_self hε)
    | succ n ih =>
      have hder : ContDiffOn ℝ n (fderiv ℝ f) (Metric.ball 0 s) :=
        hf.fderiv_of_isOpen Metric.isOpen_ball (by simp)
      obtain ⟨A, hA⟩ := c0_bounded_composition_exists s hs (fderiv ℝ f) hder.continuousOn
      have hAsmooth : ContDiffOn ℝ n A (Metric.ball (0 : C₀(ℕ, E)) s) := ih _ hder A hA
      let D : C₀(ℕ, E) → C₀(ℕ, E) →L[ℝ] (ℕ →ᵇ F) := fun w ↦ c0ToBoundedDiagonal (A w)
      have hDsmooth : ContDiffOn ℝ n D (Metric.ball (0 : C₀(ℕ, E)) s) := by
        unfold D
        exact ContDiffOn.continuousLinearMap_comp
          (G := C₀(ℕ, E) →L[ℝ] (ℕ →ᵇ F))
          (c0ToBoundedDiagonal (E := E) (F := F)) hAsmooth
      rw [Nat.cast_succ, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
        Metric.isOpen_ball.uniqueDiffOn]
      refine ⟨by simp, D, hDsmooth, fun w hw ↦ ?_⟩
      apply HasFDerivAt.hasFDerivWithinAt
      apply bounded_c0_hasFDerivAt s f (fderiv ℝ f) ?_ B hB w hw (D w) ?_ ?_
      · intro x hx
        exact (hf.differentiableOn (by simp) x hx).differentiableAt
          (Metric.isOpen_ball.mem_nhds hx) |>.hasFDerivAt
      · intro v i
        change A w i (v i) = _
        rw [hA w hw i]
      · intro ε hε
        have hg0 : ContinuousAt (fderiv ℝ f) 0 :=
          (hder.continuousOn 0 (by simpa using hs)).continuousAt
            (Metric.isOpen_ball.mem_nhds (by simpa using hs))
        have hgi (i : ℕ) : ContinuousAt (fderiv ℝ f) (w i) := by
          have hi : w i ∈ Metric.ball (0 : E) s := by
            simpa using (BoundedContinuousFunction.norm_coe_le_norm w.toBCF i).trans_lt
              (show ‖w‖ < s by simpa using hw)
          exact (hder.continuousOn _ hi).continuousAt (Metric.isOpen_ball.mem_nhds hi)
        obtain ⟨δ, hδ, hu⟩ := null_sequence_uniform_continuity (fun i ↦ w i)
          (by simpa [cocompact_eq_atTop] using zero_at_infty w) (fderiv ℝ f) hg0 hgi hε
        exact ⟨δ, hδ, fun i y hy ↦ by
          simpa [dist_eq_norm] using hu i y (by simpa [dist_eq_norm] using hy)⟩
  let e : ULift.{u} F ≃L[ℝ] F := ContinuousLinearEquiv.ulift
  let up : (ℕ →ᵇ F) →L[ℝ] (ℕ →ᵇ ULift.{u} F) :=
    e.symm.toContinuousLinearMap.compLeftContinuousBounded ℕ
  let down : (ℕ →ᵇ ULift.{u} F) →L[ℝ] (ℕ →ᵇ F) :=
    e.toContinuousLinearMap.compLeftContinuousBounded ℕ
  have hfu : ContDiffOn ℝ n (e.symm ∘ f) (Metric.ball 0 s) :=
    hf.continuousLinearMap_comp e.symm.toContinuousLinearMap
  have hbu := hmain s hs n (e.symm ∘ f) hfu (up ∘ B)
    (fun w hw i ↦ by change e.symm (B w i) = e.symm (f (w i)); rw [hB w hw i])
  have hdown := hbu.continuousLinearMap_comp down
  exact hdown.congr (fun w _ ↦ by ext i; change B w i = e (e.symm (B w i)); simp)


end HolomorphicAnosov.Analysis

