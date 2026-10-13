import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Positivity

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
universe u v

/-- Finitely many linearly independent scalar functions admit a finite set of
unisolvent samples containing any prescribed independent anchor rows. The row vectors of all evaluations span the coefficient
space: otherwise a nonzero coefficient functional would annihilate every row,
contradicting independence of the functions. Extend the anchor rows to a basis
among those rows.
Evaluation on that basis is injective, since a coefficient functional vanishing
on a basis is zero. The sample and coefficient dimensions agree, so evaluation
is bijective; finite dimensionality makes it a continuous linear equivalence.
This replaces the explicit Newton-grid existence part of Journé (1988),
pp.188–189, by finite-dimensional linear algebra, without asserting any uniform
bound over independently chosen sample sets. -/
theorem finite_unisolvent_samples {ι : Type u} {X : Type v} [Fintype ι]
    (f : ι → X → ℝ) (hf : LinearIndependent ℝ f)
    (A : Set X) (hA : LinearIndepOn ℝ (flip f) A) :
    ∃ (κ : Type v) (_ : Fintype κ) (a : κ → X),
      Function.Injective a ∧ A ⊆ Set.range a ∧ ∃ E : (ι → ℝ) ≃L[ℝ] (κ → ℝ),
        ∀ c k, E c k = ∑ i, c i * f i (a k) := by
  classical
  obtain ⟨B, _, hAB, hcover, hli⟩ :=
    exists_linearIndepOn_extension hA (Set.subset_univ A)
  let κ := B
  let a : κ → X := Subtype.val
  have ha : Function.Injective a := Subtype.val_injective
  have htop : Submodule.span ℝ (Set.range (flip f ∘ a)) = ⊤ := by
    apply top_unique
    rw [← span_flip_eq_top_iff_linearIndependent.mpr hf]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    have h := hcover ⟨x, Set.mem_univ x, rfl⟩
    simpa only [Set.image_eq_range, Function.comp_def, a, κ] using h
  let b : Module.Basis κ ℝ (ι → ℝ) := Module.Basis.mk hli htop.ge
  have hb (k : κ) : b k = flip f (a k) := Module.Basis.mk_apply _ _ k
  have : Finite κ := hli.finite
  let _ : Fintype κ := Fintype.ofFinite κ
  let E : (ι → ℝ) →ₗ[ℝ] (κ → ℝ) :=
    { toFun := fun c k ↦ ∑ i, c i * f i (a k)
      map_add' := by intro c d; ext k; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro r c; ext k; simp [mul_assoc, Finset.mul_sum] }
  have hinj : Function.Injective E := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    let φ : (ι → ℝ) →ₗ[ℝ] ℝ := ∑ i, c i • LinearMap.proj i
    have hφ : φ = 0 := b.ext fun k ↦ by
      simp only [φ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
        smul_eq_mul, LinearMap.zero_apply]
      rw [hb]
      simpa only [Function.comp_apply, flip,
        E, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] using congrFun hc k
    funext i
    have h := congrArg (fun L : (ι → ℝ) →ₗ[ℝ] ℝ ↦ L (Pi.single i 1)) hφ
    simpa [φ, LinearMap.sum_apply, LinearMap.smul_apply, Pi.single_apply] using h
  have hdim : Module.finrank ℝ (ι → ℝ) = Module.finrank ℝ (κ → ℝ) := by
    rw [Module.finrank_eq_card_basis b, Module.finrank_pi]
  let e := (LinearMap.linearEquivOfInjective E hinj hdim).toContinuousLinearEquiv
  exact ⟨κ, inferInstance, a, ha, fun x hx ↦ ⟨⟨x, hAB hx⟩, rfl⟩,
    e, fun _ _ ↦ rfl⟩

/-- Apply finite sampling to distinct real monomials while retaining the origin
and one coordinate unit vector. Their rows are independent because the constant
monomial takes value one at both anchors and that coordinate takes values zero
and one. Independence of all monomial functions follows from polynomial
extensionality and the monomial basis. -/
theorem monomial_unisolvent_samples {d : ℕ} (s : Finset (Fin d →₀ ℕ))
    (k : Fin d) (hzero : 0 ∈ s) (hunit : Finsupp.single k 1 ∈ s) :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → Fin d → ℝ),
      Function.Injective a ∧ {0, Pi.single k 1} ⊆ Set.range a ∧
      ∃ E : (s → ℝ) ≃L[ℝ] (κ → ℝ),
        ∀ c j, E c j = ∑ i : s, c i * MvPolynomial.eval (a j)
          (MvPolynomial.monomial i.val (1 : ℝ)) := by
  classical
  let L : MvPolynomial (Fin d) ℝ →ₗ[ℝ] ((Fin d → ℝ) → ℝ) :=
    LinearMap.pi fun x ↦ (MvPolynomial.aeval x).toLinearMap
  have hL : Function.Injective L := by
    intro P Q h
    apply MvPolynomial.funext
    intro x
    exact congrFun h x
  let f : s → (Fin d → ℝ) → ℝ :=
    fun i x ↦ MvPolynomial.eval x (MvPolynomial.monomial i.val (1 : ℝ))
  have hf : LinearIndependent ℝ f := by
    exact (L.linearIndependent_iff_of_injOn hL.injOn).mpr
      ((MvPolynomial.basisMonomials (Fin d) ℝ).linearIndependent.comp
        (fun i : s ↦ i.val) Subtype.val_injective)
  have hne : (0 : Fin d → ℝ) ≠ Pi.single k 1 := by
    intro h
    have := congrFun h k
    simp at this
  have hA : LinearIndepOn ℝ (flip f) {0, Pi.single k 1} := by
    apply (LinearIndepOn.pair_iff (flip f) hne).mpr
    intro c e h
    have h₀ := congrFun h ⟨0, hzero⟩
    have h₁ := congrFun h ⟨Finsupp.single k 1, hunit⟩
    have he : e = 0 := by simpa [f, flip, ← MvPolynomial.X_pow_eq_monomial] using h₁
    refine ⟨?_, he⟩
    simpa [f, flip, MvPolynomial.eval_monomial, he] using h₀
  exact finite_unisolvent_samples f hf _ hA

/-- Transpose finite arrays, with their usual supremum norms. -/
def arrayTransposeEquiv (ι κ : Type*) [Fintype ι] [Fintype κ] :
    (ι → κ → ℝ) ≃L[ℝ] (κ → ι → ℝ) :=
  ({ toFun := flip
     invFun := flip
     left_inv := fun _ ↦ rfl
     right_inv := fun _ ↦ rfl
     map_add' := fun _ _ ↦ rfl
     map_smul' := fun _ _ ↦ rfl } :
    (ι → κ → ℝ) ≃ₗ[ℝ] (κ → ι → ℝ)).toContinuousLinearEquiv

/-- Independent interpolation in each block gives the product-grid evaluation
isomorphism. Apply the second evaluation to each row, transpose, apply the first
evaluation to each resulting row, then transpose back. Expanding the two finite
sums proves the original product-monomial evaluation formula. -/
theorem product_grid_evaluation_equiv
    {ι κ I K : Type*} [Fintype ι] [Fintype κ] [Fintype I] [Fintype K]
    (F : I → ι → ℝ) (G : K → κ → ℝ)
    (EF : (ι → ℝ) ≃L[ℝ] (I → ℝ)) (EG : (κ → ℝ) ≃L[ℝ] (K → ℝ))
    (hF : ∀ c i, EF c i = ∑ j, c j * F i j)
    (hG : ∀ c i, EG c i = ∑ j, c j * G i j) :
    ∃ E : (ι → κ → ℝ) ≃L[ℝ] (I → K → ℝ),
      (∀ c i k, E c i k = ∑ a, ∑ b, c a b * F i a * G k b) ∧
      ‖E.toContinuousLinearMap‖ ≤
        ‖EF.toContinuousLinearMap‖ * ‖EG.toContinuousLinearMap‖ := by
  let E := (ContinuousLinearEquiv.piCongrRight (fun _ : ι ↦ EG)).trans
    ((arrayTransposeEquiv ι K).trans
      ((ContinuousLinearEquiv.piCongrRight (fun _ : K ↦ EF)).trans
        (arrayTransposeEquiv K I)))
  refine ⟨E, ?_, ?_⟩
  · intro c i k
    change EF (fun a ↦ EG (c a) k) i = _
    rw [hF]
    simp_rw [hG, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact mul_right_comm _ _ _
  · apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro c
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro k
    change ‖EF (fun a ↦ EG (c a) k) i‖ ≤ _
    have hv : ‖fun a ↦ EG (c a) k‖ ≤ ‖EG.toContinuousLinearMap‖ * ‖c‖ := by
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      intro a
      exact (norm_le_pi_norm (EG (c a)) k).trans
        ((EG.toContinuousLinearMap.le_opNorm (c a)).trans
          (mul_le_mul_of_nonneg_left (norm_le_pi_norm c a) (norm_nonneg _)))
    calc
      _ ≤ ‖EF (fun a ↦ EG (c a) k)‖ := norm_le_pi_norm _ _
      _ ≤ ‖EF.toContinuousLinearMap‖ * ‖fun a ↦ EG (c a) k‖ :=
        EF.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖EF.toContinuousLinearMap‖ * (‖EG.toContinuousLinearMap‖ * ‖c‖) :=
        mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ = _ := (mul_assoc _ _ _).symm

/-- Uncurry finite coefficient arrays as a continuous linear equivalence. -/
def arrayCurryEquiv (ι κ : Type*) [Fintype ι] [Fintype κ] :
    ((ι × κ) → ℝ) ≃L[ℝ] (ι → κ → ℝ) :=
  ({ toFun := Function.curry
     invFun := Function.uncurry
     left_inv := fun _ ↦ rfl
     right_inv := fun _ ↦ rfl
     map_add' := fun _ _ ↦ rfl
     map_smul' := fun _ _ ↦ rfl } :
    ((ι × κ) → ℝ) ≃ₗ[ℝ] (ι → κ → ℝ)).toContinuousLinearEquiv

/-- Product-grid sampling with one product coefficient index, suitable for
scale-weighted coefficient reconstruction. -/
theorem product_grid_flat_evaluation_equiv
    {ι κ I K : Type*} [Fintype ι] [Fintype κ] [Fintype I] [Fintype K]
    (F : I → ι → ℝ) (G : K → κ → ℝ)
    (EF : (ι → ℝ) ≃L[ℝ] (I → ℝ)) (EG : (κ → ℝ) ≃L[ℝ] (K → ℝ))
    (hF : ∀ c i, EF c i = ∑ j, c j * F i j)
    (hG : ∀ c i, EG c i = ∑ j, c j * G i j) :
    ∃ E : ((ι × κ) → ℝ) ≃L[ℝ] ((I × K) → ℝ),
      ∀ c k, E c k = ∑ j, c j * (F k.1 j.1 * G k.2 j.2) := by
  obtain ⟨E,hE,_⟩ := product_grid_evaluation_equiv F G EF EG hF hG
  refine ⟨(arrayCurryEquiv ι κ).trans (E.trans (arrayCurryEquiv I K).symm),?_⟩
  intro c k
  change E (Function.curry c) k.1 k.2 = _
  rw [hE,Fintype.sum_prod_type]
  simp only [Function.curry,mul_assoc]



end HolomorphicAnosov.JourneLeafPolynomialApproximation
