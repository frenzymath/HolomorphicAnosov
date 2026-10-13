import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

noncomputable section
open Filter _root_.Topology
namespace HolomorphicAnosov

/-- HPS, *Invariant Manifolds*, Corollary 5.3 p.60: the zero tangent section
is the only bounded invariant tangent section under the strict split gap.
For upper-to-lower maps, solve the intertwining equation on the right with
the inverse upper block; its norm shrinks by `a*k` over the forward base
step. For lower-to-upper maps solve on the left; its norm shrinks by `a*k`
over the reverse comparison. Iterate either inequality, using the inverse
base map only in the first case. Unit bounds give `(a*k)^n` upper bounds.
Geometric convergence then makes each norm zero. The lower block is never
inverted and zero fibres are included. -/
theorem parameter_graph_linear_tangent_zero
    {A : Type*} {E₁ E₂ : A → Type*}
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    (h : A ≃ A) (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p))
    (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p)) (a k : NNReal)
    (hgap : (a : ℝ) * k < 1)
    (hT₁ : ∀ p, ‖(T₁ p).symm.toContinuousLinearMap‖ ≤ a)
    (hT₂ : ∀ p, ‖T₂ p‖ ≤ k)
    (L : ∀ p, E₁ p →L[ℝ] E₂ p) (M : ∀ p, E₂ p →L[ℝ] E₁ p)
    (hL : ∀ p, ‖L p‖ ≤ 1) (hM : ∀ p, ‖M p‖ ≤ 1)
    (hLeq : ∀ p, (T₂ p).comp (L p) = (L (h p)).comp (T₁ p).toContinuousLinearMap)
    (hMeq : ∀ p, (T₁ p).toContinuousLinearMap.comp (M p) = (M (h p)).comp (T₂ p)) :
    (∀ p, L p = 0) ∧ (∀ p, M p = 0) := by
  have hLs (p : A) : ‖L (h p)‖ ≤ ((a : ℝ) * k) * ‖L p‖ := by
    have he : L (h p) = ((T₂ p).comp (L p)).comp (T₁ p).symm.toContinuousLinearMap := by
      ext x
      have hx := DFunLike.congr_fun (hLeq p) ((T₁ p).symm x)
      simpa using hx.symm
    rw [he]
    calc
      _ ≤ (‖T₂ p‖ * ‖L p‖) * ‖(T₁ p).symm.toContinuousLinearMap‖ :=
        ((T₂ p).comp (L p)).opNorm_comp_le _ |>.trans
          (mul_le_mul_of_nonneg_right ((T₂ p).opNorm_comp_le _) (norm_nonneg _))
      _ ≤ ((k : ℝ) * ‖L p‖) * a := by gcongr; exact hT₂ p; exact hT₁ p
      _ = _ := by ring
  have hMs (p : A) : ‖M p‖ ≤ ((a : ℝ) * k) * ‖M (h p)‖ := by
    have he : M p = (T₁ p).symm.toContinuousLinearMap.comp ((M (h p)).comp (T₂ p)) := by
      ext y
      have hy := congrArg (T₁ p).symm (DFunLike.congr_fun (hMeq p) y)
      simpa using hy
    rw [he]
    calc
      _ ≤ ‖(T₁ p).symm.toContinuousLinearMap‖ * (‖M (h p)‖ * ‖T₂ p‖) :=
        ((T₁ p).symm.toContinuousLinearMap.opNorm_comp_le _).trans
          (mul_le_mul_of_nonneg_left ((M (h p)).opNorm_comp_le _) (norm_nonneg _))
      _ ≤ (a : ℝ) * (‖M (h p)‖ * k) := by gcongr; exact hT₁ p; exact hT₂ p
      _ = _ := by ring
  have hq : 0 ≤ (a : ℝ) * k := mul_nonneg a.2 k.2
  have hiter : ∀ n : ℕ, (∀ p, ‖L p‖ ≤ ((a : ℝ) * k) ^ n) ∧
      (∀ p, ‖M p‖ ≤ ((a : ℝ) * k) ^ n) := by
    intro n
    induction n with
    | zero => simpa only [pow_zero] using And.intro hL hM
    | succ n ih =>
      constructor
      · intro p
        have hh := hLs (h.symm p)
        rw [h.apply_symm_apply] at hh
        exact hh.trans (by simpa only [pow_succ'] using
          mul_le_mul_of_nonneg_left (ih.1 (h.symm p)) hq)
      · intro p
        exact (hMs p).trans (by simpa only [pow_succ'] using
          mul_le_mul_of_nonneg_left (ih.2 (h p)) hq)
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hq hgap
  constructor
  · intro p
    have hn : ‖L p‖ ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Filter.Eventually.of_forall (fun n ↦ (hiter n).1 p))
    have he : ‖L p‖ = 0 := le_antisymm hn (norm_nonneg (L p))
    exact (norm_eq_zero (a := L p)).mp he
  · intro p
    have hn : ‖M p‖ ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Filter.Eventually.of_forall (fun n ↦ (hiter n).2 p))
    have he : ‖M p‖ = 0 := le_antisymm hn (norm_nonneg (M p))
    exact (norm_eq_zero (a := M p)).mp he

end HolomorphicAnosov
