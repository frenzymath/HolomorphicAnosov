import HolomorphicAnosov.Analysis.Regularity.GraphFoliationData
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

/-- Increasing a nonnegative full bound preserves the bound. -/
theorem HasFiniteHolderBounds.mono_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {α A B : ℝ} {S : Set E} {f : E → F}
    (hf : HasFiniteHolderBounds n α A f S) (hAB : A ≤ B) :
    HasFiniteHolderBounds n α B f S := by
  refine ⟨hf.1, fun j hj x hx ↦ (hf.2.1 j hj x hx).trans hAB, ?_⟩
  intro x hx y hy
  exact (hf.2.2 x hx y hy).trans
    (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (norm_nonneg _) _))

/-- Addition preserves the full finite Hölder bound with the sum constant. -/
theorem HasFiniteHolderBounds.add
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {α A B : ℝ} {S : Set E} (hS : IsOpen S) {f g : E → F}
    (hf : HasFiniteHolderBounds n α A f S) (hg : HasFiniteHolderBounds n α B g S) :
    HasFiniteHolderBounds n α (A+B) (fun x ↦ f x + g x) S := by
  have hj (j : ℕ) (hj : j ≤ n) (x : E) (hx : x ∈ S) :
      iteratedFDeriv ℝ j (fun x ↦ f x + g x) x =
        iteratedFDeriv ℝ j f x + iteratedFDeriv ℝ j g x :=
    iteratedFDeriv_add_apply ((hf.1.contDiffAt (hS.mem_nhds hx)).of_le (by exact_mod_cast hj))
      ((hg.1.contDiffAt (hS.mem_nhds hx)).of_le (by exact_mod_cast hj))
  refine ⟨hf.1.add hg.1, ?_, ?_⟩
  · intro j hji x hx
    rw [hj j hji x hx]
    exact (norm_add_le _ _).trans (add_le_add (hf.2.1 j hji x hx) (hg.2.1 j hji x hx))
  · intro x hx y hy
    rw [hj n le_rfl x hx, hj n le_rfl y hy]
    have heq : iteratedFDeriv ℝ n f x + iteratedFDeriv ℝ n g x -
        (iteratedFDeriv ℝ n f y + iteratedFDeriv ℝ n g y) =
        (iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n f y) +
        (iteratedFDeriv ℝ n g x - iteratedFDeriv ℝ n g y) := by abel
    rw [heq, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hf.2.2 x hx y hy) (hg.2.2 x hx y hy))

/-- A continuous linear output map multiplies the full Hölder bound by its norm. -/
theorem HasFiniteHolderBounds.clm_comp
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : ℕ} {α A : ℝ} {S : Set E} (hS : IsOpen S) {f : E → F}
    (hf : HasFiniteHolderBounds n α A f S) (L : F →L[ℝ] G) :
    HasFiniteHolderBounds n α (‖L‖*A) (L ∘ f) S := by
  have hj (j : ℕ) (hj : j ≤ n) (x : E) (hx : x ∈ S) :
      iteratedFDeriv ℝ j (L ∘ f) x =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ j f x) :=
    L.iteratedFDeriv_comp_left (hf.1.contDiffAt (hS.mem_nhds hx)) (by exact_mod_cast hj)
  refine ⟨hf.1.continuousLinearMap_comp L, ?_, ?_⟩
  · intro j hji x hx
    rw [hj j hji x hx]
    exact (L.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_mul_of_nonneg_left (hf.2.1 j hji x hx) (norm_nonneg _))
  · intro x hx y hy
    rw [hj n le_rfl x hx, hj n le_rfl y hy]
    have heq : L.compContinuousMultilinearMap (iteratedFDeriv ℝ n f x) -
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ n f y) =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n f y) := by
      ext v
      change L _ - L _ = L (_ - _)
      exact (map_sub L _ _).symm
    rw [heq, mul_assoc]
    exact (L.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_mul_of_nonneg_left (hf.2.2 x hx y hy) (norm_nonneg _))

/-- Constants have a full bound at every positive finite order. -/
theorem finiteHolderBounds_const
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (S : Set E) (c : F) :
    HasFiniteHolderBounds n α ‖c‖ (fun _ : E ↦ c) S := by
  refine ⟨contDiffOn_const, ?_, ?_⟩
  · intro j hj x hx
    cases j with
    | zero => simp only [norm_iteratedFDeriv_zero, le_refl]
    | succ j => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]; exact norm_nonneg c
  · intro x hx y hy
    simp only [iteratedFDeriv_const_of_ne (show n ≠ 0 by omega), Pi.zero_apply, sub_self, norm_zero]
    positivity

/-- The identity has a uniform full bound on a ball at every positive order. -/
theorem finiteHolderBounds_id_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (hn : 1 ≤ n) (α R : ℝ) :
    HasFiniteHolderBounds n α (max R 1) (id : E → E) (Metric.ball 0 R) := by
  have hj (j : ℕ) : iteratedFDeriv ℝ (j+1) (id : E → E) =
      fun x ↦ (continuousMultilinearCurryRightEquiv' ℝ j E E).symm
        (iteratedFDeriv ℝ j (fun _ : E ↦ ContinuousLinearMap.id ℝ E) x) := by
    ext x v
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp only [Function.comp_apply, fderiv_id]
  refine ⟨contDiffOn_id, ?_, ?_⟩
  · intro j hji x hx
    cases j with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact (show ‖x‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hx).le.trans
        (le_max_left _ _)
    | succ j =>
      rw [hj j]
      simp only [LinearIsometryEquiv.norm_map]
      cases j with
      | zero =>
        rw [norm_iteratedFDeriv_zero]
        exact (ContinuousLinearMap.norm_id_le).trans (le_max_right _ _)
      | succ j =>
        simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
        exact le_trans zero_le_one (le_max_right _ _)
  · intro x hx y hy
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    rw [hj j]
    have heq : iteratedFDeriv ℝ j (fun _ : E ↦ ContinuousLinearMap.id ℝ E) x =
        iteratedFDeriv ℝ j (fun _ : E ↦ ContinuousLinearMap.id ℝ E) y := by
      cases j with
      | zero => simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      | succ j => simp only [iteratedFDeriv_succ_const, Pi.zero_apply]
    dsimp only
    rw [heq, sub_self, norm_zero]
    exact mul_nonneg (le_trans zero_le_one (le_max_right _ _)) (Real.rpow_nonneg (norm_nonneg _) _)

/-- Pullback by a linear contraction preserves a full Hölder bound on any open source mapped into the original open domain. -/
theorem HasFiniteHolderBounds.comp_linear_contraction
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {α A : ℝ} {S : Set E} {T : Set D}
    (hS : IsOpen S) (_hT : IsOpen T) (hα : 0 ≤ α) (hA : 0 ≤ A)
    {f : E → F} (hf : HasFiniteHolderBounds n α A f S)
    (L : D →L[ℝ] E) (hL : ‖L‖ ≤ 1) (hm : MapsTo L T S) :
    HasFiniteHolderBounds n α A (f ∘ L) T := by
  have hopen := hS.preimage L.continuous
  have hj (j : ℕ) (hj : j ≤ n) (x : D) (hx : x ∈ T) :
      iteratedFDeriv ℝ j (f ∘ L) x =
        (iteratedFDeriv ℝ j f (L x)).compContinuousLinearMap (fun _ ↦ L) := by
    have H := L.iteratedFDerivWithin_comp_right hf.1 hS.uniqueDiffOn hopen.uniqueDiffOn
      (hm hx) (by exact_mod_cast hj)
    simpa only [iteratedFDerivWithin_of_isOpen _ hopen (hm hx),
      iteratedFDerivWithin_of_isOpen _ hS (hm hx)] using H
  have hnorm (j : ℕ) (M : ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) F) :
      ‖M.compContinuousLinearMap (fun _ ↦ L)‖ ≤ ‖M‖ := by
    apply (M.norm_compContinuousLinearMap_le _).trans
    apply mul_le_of_le_one_right (norm_nonneg _)
    exact Finset.prod_le_one₀ (fun i hi ↦ norm_nonneg L) (fun i hi ↦ hL)
  refine ⟨(hf.1.comp_continuousLinearMap L).mono hm, ?_, ?_⟩
  · intro j hji x hx
    rw [hj j hji x hx]
    exact (hnorm _ _).trans (hf.2.1 j hji (L x) (hm hx))
  · intro x hx y hy
    rw [hj n le_rfl x hx, hj n le_rfl y hy]
    have heq : (iteratedFDeriv ℝ n f (L x)).compContinuousLinearMap (fun _ ↦ L) -
        (iteratedFDeriv ℝ n f (L y)).compContinuousLinearMap (fun _ ↦ L) =
        (iteratedFDeriv ℝ n f (L x) - iteratedFDeriv ℝ n f (L y)).compContinuousLinearMap
          (fun _ ↦ L) := by ext v; rfl
    rw [heq]
    apply (hnorm _ _).trans
    apply (hf.2.2 (L x) (hm hx) (L y) (hm hy)).trans
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.rpow_le_rpow (norm_nonneg _) _ hα
    rw [← map_sub]
    exact (L.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hL)

/-- All original plaques of a fixed graph box have a common full C^{n,alpha} bound, including values, in their original ambient norm. -/
theorem graphBox_plaque_holder_bound
    {d c N n : ℕ} {α : ℝ} {Ω : Set (Block N)}
    (b : GraphBox d c N n α Ω) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ Metric.ball 0 b.transverseRadius,
      HasFiniteHolderBounds n α C (b.plaque w) (Metric.ball 0 b.leafRadius) := by
  obtain ⟨K, hK, hb⟩ := b.graph_bounds
  let L₁ := b.frame.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Block d) (Block c))
  let L₂ := b.frame.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Block d) (Block c))
  refine ⟨‖b.base‖ + ‖L₁‖ * max b.leafRadius 1 + ‖L₂‖ * K, by positivity, ?_⟩
  intro w hw
  have hi := (finiteHolderBounds_id_ball (E := Block d) n hn α b.leafRadius).clm_comp
    Metric.isOpen_ball L₁
  have hg := (hb w hw).clm_comp Metric.isOpen_ball L₂
  have h := ((finiteHolderBounds_const n hn α (Metric.ball (0 : Block d) b.leafRadius)
    b.base).add Metric.isOpen_ball hi).add Metric.isOpen_ball hg
  convert h using 1
  funext x
  dsimp [GraphBox.plaque, L₁, L₂]
  rw [add_assoc, ← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

end HolomorphicAnosov.JourneLeafPolynomialApproximation
