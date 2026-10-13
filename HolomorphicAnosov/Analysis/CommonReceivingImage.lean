import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Tactic.Linarith

/-!
# A common receiving image for uniformly approximated maps

Source: Glöckner, *Finite order differentiability properties, fixed points and implicit
functions over valued fields*, arXiv:math/0511218v2, Theorem 5.10(a)–(c), pp.45–46,
using Theorem 5.3 and Remark 5.6, pp.41–43. This is the common-ball and inverse
Lipschitz part of that argument, with continuity needed only at the chosen center.
-/

open Set Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/-- The common receiving ball and uniform inverse bound in Step 19.

Source: Glöckner, arXiv:math/0511218v2, Theorem 5.10(a)--(c), pp.45--47,
using Theorem 5.3 and Remark 5.6, Eq.(66), pp.41--43. Mathlib's guarded
closed-ball contraction theorem supplies an image ball of radius
`(‖A⁻¹‖⁻¹ - c) * ε` for every parameter. Continuity of `g p b` at the reference
parameter places these moving centers inside the concentric half-radius ball.
The triangle inequality then gives one common receiving ball. The same
two-point lower bound gives the inverse Lipschitz constant on the full image.
This conditional calculation does not assert its hypotheses for native tubes. -/
theorem common_receiving_image_of_approximates
    {P : Type*} [TopologicalSpace P]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace E]
    {g : P → E → F} {A : E ≃L[ℝ] F} {s : Set E} {c : NNReal}
    (hg : ∀ p, ApproximatesLinearOn (g p) (A : E →L[ℝ] F) s c)
    (hc : c < ‖(A.symm : F →L[ℝ] E)‖₊⁻¹)
    (hs : IsOpen s) {b : E} {ε : ℝ} {p₀ : P}
    (hε₀ : 0 < ε) (hε : Metric.closedBall b ε ⊆ s)
    (hcont : ContinuousAt (fun p ↦ g p b) p₀) :
    ∃ r : ℝ, 0 < r ∧ ∃ Q : Set P, IsOpen Q ∧ p₀ ∈ Q ∧
      ∀ p ∈ Q, ∃ e : OpenPartialHomeomorph E F,
        (e : E → F) = g p ∧ e.source = s ∧ e.target = g p '' s ∧
        Metric.closedBall (g p₀ b) r ⊆ e.target ∧
        LipschitzOnWith (‖(A.symm : F →L[ℝ] E)‖₊⁻¹ - c)⁻¹ e.symm e.target := by
  let R : ℝ := ((‖(A.symm : F →L[ℝ] E)‖₊⁻¹ : NNReal) - c) * ε
  have hgap : (0 : ℝ) < (‖(A.symm : F →L[ℝ] E)‖₊⁻¹ : NNReal) - c := by
    exact sub_pos.mpr (show (c : ℝ) < (‖(A.symm : F →L[ℝ] E)‖₊⁻¹ : NNReal) from hc)
  have hR : 0 < R := mul_pos hgap hε₀
  have hnear : ∀ᶠ p in 𝓝 p₀, g p b ∈ Metric.ball (g p₀ b) (R / 2) :=
    hcont (Metric.ball_mem_nhds (g p₀ b) (half_pos hR))
  obtain ⟨Q, hQsub, hQopen, hp₀⟩ := mem_nhds_iff.mp hnear
  refine ⟨R / 2, half_pos hR, Q, hQopen, hp₀, ?_⟩
  intro p hp
  let e := (hg p).toOpenPartialHomeomorph (g p) s (Or.inr hc) hs
  refine ⟨e, rfl, rfl, rfl, ?_, ?_⟩
  · intro z hz
    apply (hg p).closedBall_subset_target (Or.inr hc) hs hε₀.le hε
    have hz' : dist z (g p₀ b) ≤ R / 2 := hz
    have hp' : dist (g p b) (g p₀ b) < R / 2 := hQsub hp
    have htri := dist_triangle z (g p₀ b) (g p b)
    rw [dist_comm (g p₀ b) (g p b)] at htri
    change dist z (g p b) ≤ R
    linarith
  · apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro y hy z hz
    have hbound := ((hg p).antilipschitz (Or.inr hc)).le_mul_dist
      ⟨e.symm y, e.map_target hy⟩ ⟨e.symm z, e.map_target hz⟩
    change dist (e.symm y) (e.symm z) ≤
      _ * dist (e (e.symm y)) (e (e.symm z)) at hbound
    simpa only [e.right_inv hy, e.right_inv hz] using hbound


end HolomorphicAnosov.Analysis
