import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-! Rank-one cancellation for the covariant exterior expression in real coordinates. -/
noncomputable section
namespace HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport

set_option backward.isDefEq.respectTransparency false in
/-- The covariant exterior expression of a complex differentiable scalar one-form vanishes if it
annihilates the kernel of that one-form in its first slot and the connection form is of type
(1,0). (Zhang, Lemma 2.4, eq. (13), p. 7) -/
theorem coordinate_exterior_rank_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (θ : E → E →L[ℂ] ℂ) (A : E →L[ℝ] ℂ) {z : E}
    (hθ : DifferentiableAt ℂ θ z)
    (hAI : ∀ v, A (Complex.I • v) = Complex.I * A v)
    (hker : ∀ v, θ z v = 0 → ∀ w,
      fderiv ℝ θ z v w - fderiv ℝ θ z w v + A v * θ z w - A w * θ z v = 0) :
    ∀ v w, fderiv ℝ θ z v w - fderiv ℝ θ z w v +
      A v * θ z w - A w * θ z v = 0 := by
  have hD : fderiv ℝ θ z = (fderiv ℂ θ z).restrictScalars ℝ :=
    hθ.fderiv_restrictScalars ℝ
  have hD_smul (c : ℂ) (v w : E) : fderiv ℝ θ z (c • v) w = c * fderiv ℝ θ z v w := by
    rw [hD]
    change (fderiv ℂ θ z) (c • v) w = c • ((fderiv ℂ θ z) v w)
    simpa only [smul_apply, smul_eq_mul] using
      congrArg (fun L => L w) ((fderiv ℂ θ z).map_smul c v)
  have hD_smul₂ (c : ℂ) (v w : E) : fderiv ℝ θ z v (c • w) = c * fderiv ℝ θ z v w := by
    rw [hD]
    change (fderiv ℂ θ z) v (c • w) = c • ((fderiv ℂ θ z) v w)
    simpa only using (fderiv ℂ θ z v).map_smul c w
  let L : E →L[ℂ] ℂ := {
    toFun := A
    map_add' := A.map_add
    map_smul' := by
      intro c v
      have hdecomp : c • v = (c.re : ℝ) • v + (c.im : ℝ) • (Complex.I • v) := by
        calc
          c • v = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) • v := by
            rw [Complex.re_add_im]
          _ = (c.re : ℝ) • v + (c.im : ℝ) • (Complex.I • v) := by
            module
      calc
        A (c • v) = A ((c.re : ℝ) • v + (c.im : ℝ) • (Complex.I • v)) := by rw [hdecomp]
        _ = A ((c.re : ℝ) • v) + A ((c.im : ℝ) • (Complex.I • v)) := A.map_add _ _
        _ = (c.re : ℝ) • A v + (c.im : ℝ) • A (Complex.I • v) := by
          rw [A.map_smul, A.map_smul]
        _ = c • A v := by
          rw [hAI]
          conv_rhs => rw [← Complex.re_add_im c]
          simp only [Complex.real_smul]
          ring
    cont := A.continuous }
  have hA_smul (c : ℂ) (v : E) : A (c • v) = c * A v := by
    exact L.map_smul c v
  let B : E → E → ℂ := fun v w =>
    fderiv ℝ θ z v w - fderiv ℝ θ z w v + A v * θ z w - A w * θ z v
  have hB_add_left (v₁ v₂ w : E) : B (v₁ + v₂) w = B v₁ w + B v₂ w := by
    simp only [B, map_add, add_apply, add_mul, mul_add]
    ring
  have hB_add_right (v w₁ w₂ : E) : B v (w₁ + w₂) = B v w₁ + B v w₂ := by
    simp only [B, map_add, add_apply, add_mul, mul_add]
    ring
  have hB_smul_left (c : ℂ) (v w : E) : B (c • v) w = c * B v w := by
    simp only [B]
    rw [hD_smul, hD_smul₂, hA_smul, map_smul]
    ring
  have hB_smul_right (c : ℂ) (v w : E) : B v (c • w) = c * B v w := by
    simp only [B]
    rw [hD_smul₂, hD_smul, hA_smul, map_smul]
    ring
  have hB_swap (v w : E) : B v w = - B w v := by
    simp only [B]
    ring
  have hB_diag (v : E) : B v v = 0 := by
    simp [B]
  have hB_kernel : ∀ v, θ z v = 0 → ∀ w, B v w = 0 := by
    intro v hv w
    exact hker v hv w
  have hB_kernel_right : ∀ w, θ z w = 0 → ∀ v, B v w = 0 := by
    intro w hw v
    rw [hB_swap]
    exact neg_eq_zero.mpr (hB_kernel w hw v)
  by_cases hzero : θ z = 0
  · intro v w
    exact hB_kernel v (by rw [hzero]; rfl) w
  · obtain ⟨v₀, hv₀⟩ : ∃ v₀ : E, θ z v₀ ≠ 0 := by
      by_contra h
      apply hzero
      ext v
      by_contra hv
      exact h ⟨v, hv⟩
    intro v w
    let av : ℂ := θ z v / θ z v₀
    let aw : ℂ := θ z w / θ z v₀
    have hvk : θ z (v - av • v₀) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul, av]
      field_simp
      ring
    have hwk : θ z (w - aw • v₀) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul, aw]
      field_simp
      ring
    have hvdecomp : v = (v - av • v₀) + av • v₀ := by abel
    have hwdecomp : w = (w - aw • v₀) + aw • v₀ := by abel
    change B v w = 0
    rw [hvdecomp, hwdecomp, hB_add_left, hB_add_right, hB_add_right,
      hB_smul_left, hB_smul_right]
    rw [hB_kernel _ hvk, hB_kernel_right _ hwk,
      hB_smul_left, hB_smul_right, hB_diag]
    rw [hB_kernel _ hvk]
    ring

end HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
