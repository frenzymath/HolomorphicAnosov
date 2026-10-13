import HolomorphicAnosov.Analysis.BilinearHolderBound
import HolomorphicAnosov.Analysis.LowerJetHolderBound
import HolomorphicAnosov.Analysis.FDerivHolderBound
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

noncomputable section
set_option synthInstance.maxSize 2048
namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- Differentiate an actual local inverse pair of operator fields. -/
theorem fderiv_inverse_operator_field
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : D → E →L[ℝ] F} {B : D → F →L[ℝ] E} {x : D}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (hAB : ∀ᶠ z in 𝓝 x, (A z).comp (B z) = ContinuousLinearMap.id ℝ F)
    (hBA : (B x).comp (A x) = ContinuousLinearMap.id ℝ E) :
    ∀ u v, fderiv ℝ B x u v = -(B x) (fderiv ℝ A x u (B x v)) := by
  have hd := hA.hasFDerivAt.clm_comp hB.hasFDerivAt
  have hzero : (ContinuousLinearMap.compL ℝ F E F (A x)).comp (fderiv ℝ B x) +
      ((ContinuousLinearMap.compL ℝ F E F).flip (B x)).comp (fderiv ℝ A x) = 0 := by
    exact (hd.congr_of_eventuallyEq (hAB.mono fun z hz ↦ hz.symm)).unique
      (hasFDerivAt_const (ContinuousLinearMap.id ℝ F) x)
  intro u v
  have h := congrArg (fun L : D →L[ℝ] F →L[ℝ] F ↦ B x (L u v)) hzero
  have hcancel (w : E) : B x (A x w) = w :=
    congrArg (fun L : E →L[ℝ] E ↦ L w) hBA
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
    zero_apply, map_add, map_zero, hcancel] at h
  exact eq_neg_of_add_eq_zero_left h

set_option backward.isDefEq.respectTransparency false in
/-- One quantitative induction step for Hölder bounds on inverse operator families. -/
theorem inverse_operator_holder_successor
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (S : Set D) (hS : IsOpen S) (hconv : Convex ℝ S)
    (n : ℕ) (α a b k : ℝ) (hαpos : 0 < α) (hαlt : α < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (_hk : 0 ≤ k)
    (A : D → E →L[ℝ] F) (B : D → F →L[ℝ] E)
    (hA : ContDiffOn ℝ (n + 1) A S) (hB : ContDiffOn ℝ (n + 1) B S)
    (hAB : ∀ x ∈ S, (A x).comp (B x) = ContinuousLinearMap.id ℝ F)
    (hBA : ∀ x ∈ S, (B x).comp (A x) = ContinuousLinearMap.id ℝ E)
    (hBnorm : ∀ x ∈ S, ‖B x‖ ≤ k)
    (hAnorm : ∀ j ≤ n, ∀ x ∈ S, ‖iteratedFDeriv ℝ j (fderiv ℝ A) x‖ ≤ a)
    (hAhold : ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n (fderiv ℝ A) x - iteratedFDeriv ℝ n (fderiv ℝ A) y‖ ≤
        a * ‖x - y‖ ^ α)
    (hBn : ∀ j ≤ n, ∀ x ∈ S, ‖iteratedFDeriv ℝ j B x‖ ≤ b)
    (hBhold : ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n B x - iteratedFDeriv ℝ n B y‖ ≤ b * ‖x - y‖ ^ α) :
    let C := max k ((2 : ℝ) ^ (2 * (2 * n + 1)) * a * b * b)
    (∀ j ≤ n + 1, ∀ x ∈ S, ‖iteratedFDeriv ℝ j B x‖ ≤ C) ∧
    (∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ (n + 1) B x - iteratedFDeriv ℝ (n + 1) B y‖ ≤
        C * ‖x - y‖ ^ α) := by
  let : NormedAddCommGroup (F →L[ℝ] E) := inferInstance
  let : NormedSpace ℝ (F →L[ℝ] E) := inferInstance
  let : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
  let : NormedAddCommGroup (F →L[ℝ] F) := inferInstance
  let : NormedSpace ℝ (F →L[ℝ] F) := inferInstance
  let : NormedAddCommGroup (D →L[ℝ] E →L[ℝ] F) := inferInstance
  let : NormedSpace ℝ (D →L[ℝ] E →L[ℝ] F) := inferInstance
  let : NormedAddCommGroup (D →L[ℝ] F →L[ℝ] F) := inferInstance
  let : NormedSpace ℝ (D →L[ℝ] F →L[ℝ] F) := inferInstance
  let : NormedAddCommGroup (D →L[ℝ] F →L[ℝ] E) := inferInstance
  let : NormedSpace ℝ (D →L[ℝ] F →L[ℝ] E) := inferInstance
  let L₁ : (D →L[ℝ] E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) →L[ℝ] D →L[ℝ] F →L[ℝ] F :=
    (ContinuousLinearMap.compL ℝ F E F).precompL D
  let L₂ : (F →L[ℝ] E) →L[ℝ] (D →L[ℝ] F →L[ℝ] F) →L[ℝ] D →L[ℝ] F →L[ℝ] E :=
    (ContinuousLinearMap.compL ℝ F F E).precompR D
  let H₁ := fun x ↦ L₁ (fderiv ℝ A x) (B x)
  let H₂ := fun x ↦ L₂ (B x) (H₁ x)
  let c₁ := (2 : ℝ) ^ (2 * n + 1) * ‖L₁‖ * a * b
  let c₂ := (2 : ℝ) ^ (2 * n + 1) * ‖L₂‖ * b * c₁
  have hc₁ : 0 ≤ c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0 ≤ c₂ := by dsimp [c₂]; positivity
  have hDA : ContDiffOn ℝ n (fderiv ℝ A) S := hA.fderiv_of_isOpen hS (by simp)
  have hBncont : ContDiffOn ℝ n B S := hB.of_le (by exact_mod_cast Nat.le_succ n)
  obtain ⟨hH₁, hH₁norm, hH₁hold⟩ := deLaLlaveObaya_bilinear_holder_bound S hS hconv
    n α a b hαpos hαlt ha hb (fderiv ℝ A) B hDA hBncont hAnorm hBn hAhold hBhold L₁
  obtain ⟨hH₂, hH₂norm, hH₂hold⟩ := deLaLlaveObaya_bilinear_holder_bound S hS hconv
    n α b c₁ hαpos hαlt hb hc₁ B H₁ hBncont hH₁ hBn hH₁norm hBhold hH₁hold L₂
  have hDB : EqOn (fderiv ℝ B) (fun x ↦ -H₂ x) S := by
    intro x hx
    ext u v
    have hevent : ∀ᶠ z in 𝓝 x, (A z).comp (B z) = ContinuousLinearMap.id ℝ F := by
      filter_upwards [hS.mem_nhds hx] with z hz using hAB z hz
    have heq := fderiv_inverse_operator_field
      ((hA.contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp))
      ((hB.contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp))
      hevent (hBA x hx) u v
    exact heq
  have hjEq (j : ℕ) (x : D) (hx : x ∈ S) :
      iteratedFDeriv ℝ j (fderiv ℝ B) x = -iteratedFDeriv ℝ j H₂ x := by
    have h := iteratedFDerivWithin_congr (𝕜 := ℝ) hDB hx j
    rw [iteratedFDerivWithin_of_isOpen _ hS hx,
      iteratedFDerivWithin_of_isOpen _ hS hx] at h
    change iteratedFDeriv ℝ j (fderiv ℝ B) x = iteratedFDeriv ℝ j (-H₂) x at h
    rw [iteratedFDeriv_neg_apply] at h
    exact h
  have hL₁ : ‖L₁‖ ≤ 1 := (ContinuousLinearMap.norm_precompL_le _ _).trans
    (ContinuousLinearMap.norm_compL_le _ _ _ _)
  have hL₂ : ‖L₂‖ ≤ 1 := (ContinuousLinearMap.norm_precompR_le _ _).trans
    (ContinuousLinearMap.norm_compL_le _ _ _ _)
  have hbound : c₂ ≤ (2 : ℝ) ^ (2 * (2 * n + 1)) * a * b * b := by
    dsimp [c₂, c₁]
    calc
      _ ≤ (2 : ℝ) ^ (2 * n + 1) * 1 * b *
          ((2 : ℝ) ^ (2 * n + 1) * 1 * a * b) := by gcongr
      _ = _ := by
        rw [show 2 * (2 * n + 1) = (2 * n + 1) + (2 * n + 1) by omega, pow_add]
        ring
  dsimp only
  constructor
  · intro j hj x hx
    cases j with
    | zero => simpa only [norm_iteratedFDeriv_zero] using (hBnorm x hx).trans (le_max_left _ _)
    | succ j =>
      rw [← norm_iteratedFDeriv_fderiv, hjEq j x hx, norm_neg]
      exact (hH₂norm j (by omega) x hx).trans (hbound.trans (le_max_right _ _))
  · intro x hx y hy
    rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
    simp only [Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map]
    rw [hjEq n x hx, hjEq n y hy, neg_sub_neg, norm_sub_rev]
    exact (hH₂hold x hx y hy).trans (mul_le_mul_of_nonneg_right
      (hbound.trans (le_max_right _ _)) (Real.rpow_nonneg (norm_nonneg _) _))

/-- A uniform finite-order Hölder bound for inverse operator fields on an open convex domain. -/
theorem inverse_operator_holder_bound
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) (α a k : ℝ) (hαpos : 0 < α) (hαlt : α < 1)
    (ha : 0 ≤ a) (hk : 0 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Set D), IsOpen S → Convex ℝ S →
      ∀ (A : D → E →L[ℝ] F) (B : D → F →L[ℝ] E),
      ContDiffOn ℝ n A S → ContDiffOn ℝ n B S →
      (∀ x ∈ S, (A x).comp (B x) = ContinuousLinearMap.id ℝ F) →
      (∀ x ∈ S, (B x).comp (A x) = ContinuousLinearMap.id ℝ E) →
      (∀ x ∈ S, ‖B x‖ ≤ k) →
      (∀ j ≤ n, ∀ x ∈ S, ‖iteratedFDeriv ℝ j A x‖ ≤ a) →
      (∀ x ∈ S, ∀ y ∈ S,
        ‖iteratedFDeriv ℝ n A x - iteratedFDeriv ℝ n A y‖ ≤ a * ‖x - y‖ ^ α) →
      (∀ j ≤ n, ∀ x ∈ S, ‖iteratedFDeriv ℝ j B x‖ ≤ C) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        ‖iteratedFDeriv ℝ n B x - iteratedFDeriv ℝ n B y‖ ≤ C * ‖x - y‖ ^ α) := by
  induction n generalizing a with
  | zero =>
    refine ⟨max k (k * k * a), le_max_of_le_left hk, ?_⟩
    intro S hS hconv A B hA hB hAB hBA hBnorm hAnorm hAhold
    constructor
    · intro j hj x hx
      have hj0 : j = 0 := by omega
      subst j
      simpa only [norm_iteratedFDeriv_zero] using (hBnorm x hx).trans (le_max_left _ _)
    · intro x hx y hy
      have hdiff : B x - B y = ((B x).comp (A y - A x)).comp (B y) := by
        rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
          ContinuousLinearMap.comp_assoc, hAB y hy, hBA x hx]
        simp
      have hAh := hAhold x hx y hy
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
        LinearIsometryEquiv.norm_map] at hAh ⊢
      rw [hdiff]
      calc
        _ ≤ (‖B x‖ * ‖A y - A x‖) * ‖B y‖ :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
        _ ≤ (k * (a * ‖x - y‖ ^ α)) * k := by
          gcongr
          · exact hBnorm x hx
          · simpa only [norm_sub_rev] using hAh
          · exact hBnorm y hy
        _ = (k * k * a) * ‖x - y‖ ^ α := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg (norm_nonneg _) _)
  | succ n ih =>
    obtain ⟨b, hb, hbound⟩ := ih (2 * a) (by positivity)
    refine ⟨max k ((2 : ℝ) ^ (2 * (2 * n + 1)) * a * b * b),
      le_max_of_le_left hk, ?_⟩
    intro S hS hconv A B hA hB hAB hBA hBnorm hAnorm hAhold
    have hAn : ContDiffOn ℝ n A S := hA.of_le (by exact_mod_cast Nat.le_succ n)
    have hBn : ContDiffOn ℝ n B S := hB.of_le (by exact_mod_cast Nat.le_succ n)
    have hAlower : ∀ x ∈ S, ∀ y ∈ S,
        ‖iteratedFDeriv ℝ n A x - iteratedFDeriv ℝ n A y‖ ≤ (2 * a) * ‖x - y‖ ^ α := by
      intro x hx y hy
      have h := lower_jet_holder_bound S hS hconv (n+1) α a hαpos hαlt.le ha A hA
        (fun j hj z hz ↦ by
          rw [iteratedFDerivWithin_of_isOpen _ hS hz]
          exact hAnorm j hj z hz) n (Nat.lt_succ_self n) x hx y hy
      simpa only [iteratedFDerivWithin_of_isOpen _ hS hx,
        iteratedFDerivWithin_of_isOpen _ hS hy] using h
    obtain ⟨hBjets, hBholder⟩ := hbound S hS hconv A B hAn hBn hAB hBA hBnorm
      (fun j hj x hx ↦ (hAnorm j (by omega) x hx).trans (by linarith)) hAlower
    obtain ⟨_, hDAjets, hDAholder⟩ := fderiv_holder_bound S hS n A hA a α hAnorm hAhold
    exact inverse_operator_holder_successor S hS hconv n α a b k hαpos hαlt ha hb hk
      A B hA hB hAB hBA hBnorm hDAjets hDAholder hBjets hBholder

end HolomorphicAnosov
