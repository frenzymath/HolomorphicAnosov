import HolomorphicAnosov.Analysis.Regularity.JournePerturbedInterpolation
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation

/-- Stable interpolation on a scaled homogeneous sampling grid controls the weighted coefficient update by the residual sampled on the new grid. (Journé, 1988) -/
theorem weighted_interpolation_residual_bound
    {ι κ X : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i)) (degree : ι → ℕ)
    (hhom : ∀ i (t : ℝ) (x : X), f i (t • x) = t^(degree i)*f i x)
    (a : κ → X) (E₀ : (ι → ℝ) ≃L[ℝ] (κ → ℝ))
    (hE₀ : ∀ c k, E₀ c k = ∑ i, c i*f i (a k)) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ b : κ → X, ‖b-a‖ < δ →
      ∀ (t : ℝ), 0 < t → ∀ (h : X → ℝ) (c : ι → ℝ) (M : ℝ), 0 ≤ M →
      (∀ k, |h (t • b k)-∑ i, c i*f i (t • b k)| ≤ M) →
      ∃ c' : ι → ℝ,
        (∀ k, ∑ i, c' i*f i (t • b k) = h (t • b k)) ∧
        ∑ i, |c' i-c i| *t^(degree i) ≤ C*M := by
  classical
  obtain ⟨δ,hδ,H⟩ := finite_sampling_stable f hf a E₀ hE₀
  refine ⟨δ,(Fintype.card ι:ℝ)*(2*‖E₀.symm.toContinuousLinearMap‖),hδ,by positivity,?_⟩
  intro b hb t ht h c M hM hres
  obtain ⟨T,hTright,hTleft,hTnorm⟩ := H b hb
  let r : κ → ℝ := fun k ↦ h (t • b k)-∑ i, c i*f i (t • b k)
  let c' : ι → ℝ := fun i ↦ c i+(t^(degree i))⁻¹*(T r i)
  have hscale (i : ι) : (t^(degree i))⁻¹*t^(degree i) = 1 :=
    inv_mul_cancel₀ (pow_ne_zero _ ht.ne')
  have hr : ‖r‖ ≤ M := by
    apply (pi_norm_le_iff_of_nonneg hM).mpr
    intro k
    exact hres k
  have hcoef (i : ι) : |c' i-c i| *t^(degree i) = |T r i| := by
    dsimp [c']
    rw [add_sub_cancel_left,abs_mul,abs_inv,abs_of_pos (pow_pos ht _)]
    calc
      (t^degree i)⁻¹*|T r i| *t^degree i = ((t^degree i)⁻¹*t^degree i)*|T r i| := by ring
      _ = _ := by rw [hscale,one_mul]
  refine ⟨c',?_,?_⟩
  · intro k
    have hterm (i : ι) : c' i*f i (t • b k) =
        c i*f i (t • b k)+(T r i)*f i (b k) := by
      dsimp [c']
      rw [add_mul,hhom]
      have hcalc : (t^degree i)⁻¹*(T r i)*(t^degree i*f i (b k)) =
          ((t^degree i)⁻¹*t^degree i)*((T r i)*f i (b k)) := by ring
      rw [hcalc,hscale,one_mul]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib,hTright]
    dsimp [r]
    ring
  · simp_rw [hcoef]
    have hbnd (i : ι) : |T r i| ≤ (2*‖E₀.symm.toContinuousLinearMap‖)*M := by
      have hi : |T r i| ≤ ‖T r‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (T r) i
      exact hi.trans ((T.le_opNorm r).trans
        (mul_le_mul hTnorm hr (norm_nonneg _) (by positivity)))
    calc
      ∑ i, |T r i| ≤ ∑ _ : ι, (2*‖E₀.symm.toContinuousLinearMap‖)*M :=
        Finset.sum_le_sum (fun i _ ↦ hbnd i)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

/-- At a fixed moved grid and positive scale, the interpolating coefficients are unique. -/
theorem scaled_interpolation_unique
    {ι κ X : Type*} [Fintype ι] [Fintype κ] [SMul ℝ X]
    (f : ι → X → ℝ) (degree : ι → ℕ)
    (hhom : ∀ i (t : ℝ) (x : X), f i (t • x) = t^(degree i)*f i x)
    (b : κ → X) (T : (κ → ℝ) →L[ℝ] (ι → ℝ))
    (hleft : ∀ c, T (fun k ↦ ∑ i, c i*f i (b k)) = c)
    {t : ℝ} (ht : 0 < t) (c c' : ι → ℝ)
    (heval : ∀ k, (∑ i, c i*f i (t • b k)) = ∑ i, c' i*f i (t • b k)) : c = c' := by
  have he (v : ι → ℝ) (k : κ) :
      (∑ i, (v i*t^(degree i))*f i (b k)) = ∑ i, v i*f i (t • b k) := by
    simp_rw [hhom,mul_assoc]
  have hdata : (fun k ↦ ∑ i, (c i*t^(degree i))*f i (b k)) =
      (fun k ↦ ∑ i, (c' i*t^(degree i))*f i (b k)) := by
    funext k
    rw [he,he]
    exact heval k
  have hcoef := congrArg T hdata
  rw [hleft,hleft] at hcoef
  funext i
  exact mul_right_cancel₀ (pow_ne_zero _ ht.ne') (congrFun hcoef i)

/-- Choose an interpolant once at each scale. -/
theorem stable_scaled_interpolant
    {ι κ X : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i)) (degree : ι → ℕ)
    (hhom : ∀ i (t : ℝ) (x : X), f i (t • x) = t^(degree i)*f i x)
    (a : κ → X) (E₀ : (ι → ℝ) ≃L[ℝ] (κ → ℝ))
    (hE₀ : ∀ c k, E₀ c k = ∑ i, c i*f i (a k)) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ b : κ → X, ‖b-a‖ < δ →
      ∀ (t : ℝ), 0 < t → ∀ h : X → ℝ, ∃ c : ι → ℝ,
        (∀ k, ∑ i, c i*f i (t • b k) = h (t • b k)) ∧
        ∀ (v : ι → ℝ) (M : ℝ), 0 ≤ M →
          (∀ k, |h (t • b k)-∑ i, v i*f i (t • b k)| ≤ M) →
          ∑ i, |c i-v i| *t^(degree i) ≤ C*M := by
  classical
  obtain ⟨δ₁,hδ₁,H₁⟩ := finite_sampling_stable f hf a E₀ hE₀
  obtain ⟨δ₂,C,hδ₂,hC,H₂⟩ := weighted_interpolation_residual_bound f hf degree hhom a E₀ hE₀
  refine ⟨min δ₁ δ₂,C,lt_min hδ₁ hδ₂,hC,?_⟩
  intro b hb t ht h
  obtain ⟨T,hr,hl,_⟩ := H₁ b (hb.trans_le (min_le_left _ _))
  let c : ι → ℝ := fun i ↦ (t^degree i)⁻¹*T (fun k ↦ h (t • b k)) i
  have heval (k : κ) : ∑ i, c i*f i (t • b k) = h (t • b k) := by
    have he (i : ι) : c i*f i (t • b k) = T (fun k ↦ h (t • b k)) i*f i (b k) := by
      dsimp [c]
      rw [hhom]
      field_simp
    simp_rw [he]
    exact hr _ k
  refine ⟨c,heval,?_⟩
  intro v M hM hres
  obtain ⟨c',hc',hbound⟩ := H₂ b (hb.trans_le (min_le_right _ _)) t ht h v M hM hres
  have heq : c = c' := scaled_interpolation_unique f degree hhom b T hl ht c c'
    (fun k ↦ (heval k).trans (hc' k).symm)
  simpa only [heq] using hbound

/-- The same stable sampling inverse controls evaluation throughout any fixed compact region. -/
theorem stable_interpolation_evaluation_bound
    {ι κ X : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i))
    (a : κ → X) (E₀ : (ι → ℝ) ≃L[ℝ] (κ → ℝ))
    (hE₀ : ∀ c k, E₀ c k = ∑ i, c i*f i (a k))
    (S : Set X) (hS : IsCompact S) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 ≤ L ∧ ∀ b : κ → X, ‖b-a‖ < δ →
      ∀ (c : ι → ℝ) (M : ℝ), 0 ≤ M →
      (∀ k, |∑ i, c i*f i (b k)| ≤ M) → ∀ y ∈ S,
        |∑ i, c i*f i y| ≤ L*M := by
  classical
  obtain ⟨δ,hδ,H⟩ := finite_sampling_stable f hf a E₀ hE₀
  obtain ⟨B,hB⟩ := hS.exists_bound_of_continuousOn
    (continuous_pi hf).continuousOn
  let N := 2*‖E₀.symm.toContinuousLinearMap‖
  refine ⟨δ,(Fintype.card ι:ℝ)*N*max B 0,hδ,by dsimp [N]; positivity,?_⟩
  intro b hb c M hM hc y hy
  obtain ⟨T,_,hleft,hnorm⟩ := H b hb
  let v : κ → ℝ := fun k ↦ ∑ i, c i*f i (b k)
  have hv : ‖v‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).mpr hc
  have hcn : ‖c‖ ≤ N*M := by
    rw [← hleft c]
    exact (T.le_opNorm v).trans (mul_le_mul hnorm hv (norm_nonneg _) (by dsimp [N]; positivity))
  have hfi (i : ι) : |f i y| ≤ max B 0 :=
    (show |f i y| ≤ ‖fun j ↦ f j y‖ from by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun j : ι ↦ f j y) i).trans
      ((hB y hy).trans (le_max_left _ _))
  have hci (i : ι) : |c i| ≤ N*M := (norm_le_pi_norm c i).trans hcn
  calc
    |∑ i, c i*f i y| ≤ ∑ i, |c i*f i y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : ι, (N*M)*max B 0 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hci i) (hfi i) (abs_nonneg _) (by dsimp [N]; positivity)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end HolomorphicAnosov.JourneLeafPolynomialApproximation
