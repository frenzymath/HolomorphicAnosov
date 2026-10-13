import HolomorphicAnosov.Analysis.Regularity.EuclideanPolynomialMixedPartial
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-!
# Affine transport of the polynomial mixed-partial coefficient

This isolates the final algebraic identity used after normalizing a ball by
`x = a + ρ y`.  The substitution is made inside the same multivariate
polynomial ring, so the identity retains the public `MvPolynomial` and
`euclideanPolynomialMixedPartial` notions exactly.
-/
noncomputable section
open scoped BigOperators

namespace HolomorphicAnosov.Analysis.Regularity

lemma euclideanCoordinatePartial_eval_pderiv_g3 {N : ℕ} (P : MvPolynomial (Fin N) ℝ) (i : Fin N)
    (x : EuclideanSpace ℝ (Fin N)) :
    euclideanCoordinatePartial i (euclideanPolynomialEval P) x =
      MvPolynomial.eval (fun j ↦ x j) (MvPolynomial.pderiv i P) := by
  rw [euclideanCoordinatePartial]
  apply HasDerivAt.deriv
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp only [euclideanPolynomialEval, MvPolynomial.eval_C]
      simpa using (hasDerivAt_const (x := (0 : ℝ)) c)
  | add P Q hP hQ =>
      convert hP.add hQ using 1
      · funext t
        simp [euclideanPolynomialEval, MvPolynomial.eval_add]
      · simp [MvPolynomial.eval_add]
  | mul_X P j hP =>
      by_cases hij : i = j
      · have hji : j = i := hij.symm
        have hX : HasDerivAt
            (fun t : ℝ => (x + t • EuclideanSpace.single i (1 : ℝ)).ofLp j)
            1 0 := by
          subst j
          convert (hasDerivAt_const (x := (0 : ℝ)) (x i)).add
            ((hasDerivAt_id (x := (0 : ℝ))).const_mul 1) using 1
          funext t
          simp [one_mul]
          norm_num
        convert hP.mul hX using 1
        · funext t
          simp [euclideanPolynomialEval, MvPolynomial.eval_mul, MvPolynomial.eval_X]
        · simp [MvPolynomial.pderiv_X, MvPolynomial.eval_add,
            MvPolynomial.eval_mul, hji]
          simp [euclideanPolynomialEval, add_comm]
          ring
      · have hji : j ≠ i := Ne.symm hij
        have hX : HasDerivAt
            (fun t : ℝ => (x + t • EuclideanSpace.single i (1 : ℝ)).ofLp j)
            0 0 := by
          simp [hji]
          simpa using (hasDerivAt_const (x := (0 : ℝ)) (x j))
        convert hP.mul hX using 1
        · funext t
          simp [euclideanPolynomialEval, MvPolynomial.eval_mul, MvPolynomial.eval_X]
        · simp [MvPolynomial.pderiv_X, MvPolynomial.eval_mul, hij]
          ring

lemma pderiv_subst {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) (ρ : ℝ) (i : Fin N) :
    MvPolynomial.pderiv i
      (MvPolynomial.eval₂Hom (MvPolynomial.C : ℝ →+* MvPolynomial (Fin N) ℝ)
        (fun j => MvPolynomial.C (a j) + MvPolynomial.C ρ * MvPolynomial.X j) P) =
      MvPolynomial.C ρ *
        (MvPolynomial.eval₂Hom (MvPolynomial.C : ℝ →+* MvPolynomial (Fin N) ℝ)
          (fun j => MvPolynomial.C (a j) + MvPolynomial.C ρ * MvPolynomial.X j)
          (MvPolynomial.pderiv i P)) := by
  let S : MvPolynomial (Fin N) ℝ →+* MvPolynomial (Fin N) ℝ :=
    MvPolynomial.eval₂Hom (MvPolynomial.C : ℝ →+* MvPolynomial (Fin N) ℝ)
      (fun j => MvPolynomial.C (a j) + MvPolynomial.C ρ * MvPolynomial.X j)
  change MvPolynomial.pderiv i (S P) = MvPolynomial.C ρ * S (MvPolynomial.pderiv i P)
  induction P using MvPolynomial.induction_on with
  | C c => simp [S]
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ, mul_add]
  | mul_X P j hP =>
      rw [map_mul]
      rw [MvPolynomial.pderiv_mul, hP]
      by_cases hij : i = j
      · subst j
        simp [S, MvPolynomial.pderiv_X, RingHom.map_add, RingHom.map_mul,
          Pi.single_eq_same]
        ring
      · have hji : j ≠ i := Ne.symm hij
        simp [S, MvPolynomial.pderiv_X, RingHom.map_mul, Pi.single_eq_of_ne hji]
        ring


lemma partial_iterate_eval {N : ℕ} (P : MvPolynomial (Fin N) ℝ) (i : Fin N)
    (k : ℕ) (x : EuclideanSpace ℝ (Fin N)) :
    ((euclideanCoordinatePartial i)^[k] (euclideanPolynomialEval P)) x =
      MvPolynomial.eval (fun j ↦ x j) ((MvPolynomial.pderiv i)^[k] P) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      rw [show ((euclideanCoordinatePartial i)^[k] (euclideanPolynomialEval P)) =
        euclideanPolynomialEval ((MvPolynomial.pderiv i)^[k] P) by
          funext y; exact ih y]
      simpa [Function.iterate_succ_apply'] using
        (euclideanCoordinatePartial_eval_pderiv_g3 ((MvPolynomial.pderiv i)^[k] P) i x)

lemma mixed_eval_fold {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (β : Fin N → ℕ) (x : EuclideanSpace ℝ (Fin N)) :
    euclideanPolynomialMixedPartial P β x =
      MvPolynomial.eval (fun j ↦ x j)
        ((List.finRange N).foldl
          (fun Q i ↦ (MvPolynomial.pderiv i)^[β i] Q) P) := by
  unfold euclideanPolynomialMixedPartial
  let F : (Fin N → ℝ) → MvPolynomial (Fin N) ℝ → ℝ :=
    fun z Q ↦ MvPolynomial.eval z Q
  have hfold : ∀ (L : List (Fin N)) (Q : MvPolynomial (Fin N) ℝ),
      (L.foldl (fun f i ↦ (euclideanCoordinatePartial i)^[β i] f)
        (euclideanPolynomialEval Q)) x =
      (L.foldl (fun Q i ↦ (MvPolynomial.pderiv i)^[β i] Q) Q).eval (fun j ↦ x j) := by
    intro L
    induction L with
    | nil => intro Q; rfl
    | cons i L ih =>
        intro Q
        simp only [List.foldl]
        have heq : (euclideanCoordinatePartial i)^[β i] (euclideanPolynomialEval Q) =
            euclideanPolynomialEval ((MvPolynomial.pderiv i)^[β i] Q) := by
          funext y
          exact partial_iterate_eval Q i (β i) y
        rw [heq]
        exact ih ((MvPolynomial.pderiv i)^[β i] Q)
  exact hfold (List.finRange N) P


lemma pderiv_iterate_subst {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) (ρ : ℝ) (i : Fin N) (k : ℕ) :
    (MvPolynomial.pderiv i)^[k]
      (MvPolynomial.eval₂Hom (MvPolynomial.C : ℝ →+* MvPolynomial (Fin N) ℝ)
        (fun j => MvPolynomial.C (a j) + MvPolynomial.C ρ * MvPolynomial.X j) P) =
      MvPolynomial.C (ρ ^ k) *
        (MvPolynomial.eval₂Hom (MvPolynomial.C : ℝ →+* MvPolynomial (Fin N) ℝ)
          (fun j => MvPolynomial.C (a j) + MvPolynomial.C ρ * MvPolynomial.X j)
          ((MvPolynomial.pderiv i)^[k] P)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      rw [MvPolynomial.pderiv_C_mul]
      rw [pderiv_subst]
      rw [Function.iterate_succ_apply']
      simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]

lemma subst_eval_zero {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) (ρ : ℝ) :
    MvPolynomial.eval (fun _ => 0)
      (MvPolynomial.eval₂Hom (MvPolynomial.C : ℝ →+* MvPolynomial (Fin N) ℝ)
        (fun j => MvPolynomial.C (a j) + MvPolynomial.C ρ * MvPolynomial.X j) P) =
      MvPolynomial.eval (fun j => a j) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simpa [map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
      simp only [map_mul, MvPolynomial.eval₂Hom_X']
      rw [hP]
      simp [MvPolynomial.eval_X]


lemma foldl_add_zero {ι : Type*} (L : List ι)
    (f : ι → ℕ) (n : ℕ) :
    L.foldl (fun q i => q + f i) n = n + L.foldl (fun q i => q + f i) 0 := by
  induction L generalizing n with
  | nil => simp
  | cons i L ih =>
      simp only [List.foldl]
      rw [ih]
      simpa [Nat.add_assoc] using congrArg (fun z => n + z) (ih (f i)).symm

lemma pderiv_iterate_const_mul {N : ℕ} (c : ℝ) (Q : MvPolynomial (Fin N) ℝ)
    (i : Fin N) (k : ℕ) :
    (MvPolynomial.pderiv i)^[k] (MvPolynomial.C c * Q) =
      MvPolynomial.C c * (MvPolynomial.pderiv i)^[k] Q := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, MvPolynomial.pderiv_C_mul]
      simp [Function.iterate_succ_apply']

lemma foldl_const_mul {N : ℕ} (L : List (Fin N))
    (c : ℝ) (Q : MvPolynomial (Fin N) ℝ) (β : Fin N → ℕ) :
    L.foldl (fun Q i => (MvPolynomial.pderiv i)^[β i] Q) (MvPolynomial.C c * Q) =
      MvPolynomial.C c * L.foldl (fun Q i => (MvPolynomial.pderiv i)^[β i] Q) Q := by
  induction L generalizing Q with
  | nil => simp
  | cons i L ih =>
      simp only [List.foldl]
      rw [pderiv_iterate_const_mul]
      exact ih ((MvPolynomial.pderiv i)^[β i] Q)

lemma fold_subst {N : ℕ} (L : List (Fin N))
    (P : MvPolynomial (Fin N) ℝ) (a : EuclideanSpace ℝ (Fin N))
    (ρ : ℝ) (β : Fin N → ℕ) :
    L.foldl (fun Q i => (MvPolynomial.pderiv i)^[β i] Q)
      (MvPolynomial.eval₂Hom (MvPolynomial.C : ℝ →+* MvPolynomial (Fin N) ℝ)
        (fun j => MvPolynomial.C (a j) + MvPolynomial.C ρ * MvPolynomial.X j) P) =
      MvPolynomial.C (ρ ^ (L.foldl (fun n i => n + β i) 0)) *
      MvPolynomial.eval₂Hom (MvPolynomial.C : ℝ →+* MvPolynomial (Fin N) ℝ)
        (fun j => MvPolynomial.C (a j) + MvPolynomial.C ρ * MvPolynomial.X j)
        (L.foldl (fun Q i => (MvPolynomial.pderiv i)^[β i] Q) P) := by
  induction L generalizing P with
  | nil => simp
  | cons i L ih =>
      simp only [List.foldl]
      rw [pderiv_iterate_subst]
      rw [foldl_const_mul]
      rw [ih ((MvPolynomial.pderiv i)^[β i] P)]
      rw [foldl_add_zero]
      simp only [zero_add]
      rw [← mul_assoc, ← MvPolynomial.C_mul]
      congr 2
      rw [← pow_add]
      congr 1
      simpa [Nat.add_assoc] using (foldl_add_zero L β (β i)).symm

lemma fold_sum_finRange {N : ℕ} (β : Fin N → ℕ) :
    (List.finRange N).foldl (fun n i => n + β i) 0 = ∑ i, β i := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.finRange_succ]
      simp only [List.foldl]
      rw [List.foldl_map]
      rw [foldl_add_zero]
      rw [ih (fun i => β i.succ)]
      rw [Fin.sum_univ_succ]
      simp

/-- Mixed partials of the affine pullback `Q(y)=P(a+ρ y)` scale by
`ρ ^ |β|` at the origin. -/
theorem euclideanPolynomialMixedPartial_affine_identity_g3
    {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) (ρ : ℝ) (β : Fin N → ℕ) :
    let vars : Fin N → MvPolynomial (Fin N) ℝ :=
      fun i => MvPolynomial.C (a i) + MvPolynomial.C ρ * MvPolynomial.X i
    let Q : MvPolynomial (Fin N) ℝ :=
      MvPolynomial.eval₂Hom (MvPolynomial.C : ℝ →+* MvPolynomial (Fin N) ℝ) vars P
    euclideanPolynomialMixedPartial Q β 0 =
      ρ ^ (∑ i, β i) * euclideanPolynomialMixedPartial P β a := by
  change euclideanPolynomialMixedPartial
      (MvPolynomial.eval₂Hom (MvPolynomial.C : ℝ →+* MvPolynomial (Fin N) ℝ)
        (fun i => MvPolynomial.C (a i) + MvPolynomial.C ρ * MvPolynomial.X i) P) β 0 =
    ρ ^ (∑ i, β i) * euclideanPolynomialMixedPartial P β a
  rw [mixed_eval_fold]
  rw [fold_subst]
  rw [fold_sum_finRange]
  rw [mixed_eval_fold]
  rw [MvPolynomial.eval_mul]
  simp only [MvPolynomial.eval_C]
  have hz := subst_eval_zero
    ((List.finRange N).foldl (fun Q i => (MvPolynomial.pderiv i)^[β i] Q) P) a ρ
  have hz' :
      MvPolynomial.eval (fun j => WithLp.ofLp (0 : EuclideanSpace ℝ (Fin N)) j)
        ((MvPolynomial.eval₂Hom (MvPolynomial.C : ℝ →+* MvPolynomial (Fin N) ℝ)
          (fun j => MvPolynomial.C (a j) + MvPolynomial.C ρ * MvPolynomial.X j)
          ((List.finRange N).foldl (fun Q i => (MvPolynomial.pderiv i)^[β i] Q) P))) =
      MvPolynomial.eval (fun j => a j)
        ((List.finRange N).foldl (fun Q i => (MvPolynomial.pderiv i)^[β i] Q) P) := by
    simpa using hz
  rw [hz']

end HolomorphicAnosov.Analysis.Regularity
