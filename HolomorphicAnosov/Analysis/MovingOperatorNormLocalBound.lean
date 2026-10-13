import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

noncomputable section
open Set Filter
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
universe u v w z

/-- A strict original operator-norm bound persists locally in a finite frame.

Choose `q` strictly between the norm at `x₀` and `c`. On the fixed compact unit
sphere in `V`, the original frame vector is nonzero, so the operator inequality
at `x₀` gives the strict inequality `‖A(frame v)‖ < q * ‖frame v‖`.
Joint continuity makes this inequality hold near each `(x₀,v)`; compactness
makes the base neighborhood uniform over the sphere. Normalize every nonzero
frame coordinate, use real homogeneity of both original norms, and cancel the
positive normalization factor to obtain the same bound on every fibre vector.
Mathlib's `opNorm_le_bound` gives the conclusion. A zero coordinate is handled
directly; this includes a zero-dimensional source, whose sphere is empty.
No nonempty-sphere or positive-rank hypothesis is used.
-/
theorem moving_operator_norm_eventually_le
    {B : Type u} [TopologicalSpace B]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {E : B → Type w} {F : B → Type z}
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℝ (F x)]
    (frame : ∀ x, V ≃ₗ[ℝ] E x) (A : ∀ x, E x →L[ℝ] F x)
    (hsource : Continuous (fun p : B × V ↦ ‖frame p.1 p.2‖))
    (himage : Continuous (fun p : B × V ↦ ‖A p.1 (frame p.1 p.2)‖))
    (x₀ : B) {c : ℝ} (hc : ‖A x₀‖ < c) :
    ∃ q : ℝ, q < c ∧ ∀ᶠ x in 𝓝 x₀, ‖A x‖ ≤ q := by
  obtain ⟨q, hq, hqc⟩ := exists_between hc
  have hqnonneg : 0 ≤ q := (norm_nonneg (A x₀)).trans hq.le
  have huniform : ∀ᶠ x in 𝓝 x₀, ∀ v ∈ Metric.sphere (0 : V) 1,
      ‖A x (frame x v)‖ < q * ‖frame x v‖ := by
    apply (isCompact_sphere (0 : V) 1).eventually_forall_of_forall_eventually
    intro v hv
    have hvnorm : ‖v‖ = 1 := by simpa using hv
    have hvne : v ≠ 0 := by
      intro h
      simp [h] at hvnorm
    have hframene : frame x₀ v ≠ 0 := by
      intro h
      apply hvne
      exact (frame x₀).injective (by simpa using h)
    have hstrict : ‖A x₀ (frame x₀ v)‖ < q * ‖frame x₀ v‖ :=
      (A x₀).le_opNorm (frame x₀ v) |>.trans_lt
        (mul_lt_mul_of_pos_right hq (norm_pos_iff.mpr hframene))
    exact himage.continuousAt.eventually_lt
      (continuous_const.mul hsource).continuousAt hstrict
  refine ⟨q, hqc, huniform.mono ?_⟩
  intro x hx
  apply (A x).opNorm_le_bound hqnonneg
  intro w
  obtain ⟨v, rfl⟩ := (frame x).surjective w
  by_cases hv : v = 0
  · simp [hv]
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let u : V := ‖v‖⁻¹ • v
  have hunorm : ‖u‖ = 1 := by
    simp [u, norm_smul, hvnorm]
  have hu : u ∈ Metric.sphere (0 : V) 1 := by simpa using hunorm
  have hscaled : ‖v‖⁻¹ * ‖A x (frame x v)‖ ≤
      ‖v‖⁻¹ * (q * ‖frame x v‖) := by
    simpa [u, norm_smul, mul_assoc, mul_comm, mul_left_comm] using (hx u hu).le
  exact (mul_le_mul_iff_right₀ (inv_pos.mpr (norm_pos_iff.mpr hv))).mp
    (by simpa [mul_comm] using hscaled)

end HolomorphicAnosov
