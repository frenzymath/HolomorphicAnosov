import HolomorphicAnosov.Analysis.Regularity.JournePlaqueHigherHolder
import HolomorphicAnosov.Analysis.BilinearHolderBound
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Finite products and differences in the full Hölder bound

DAG node: `analysis.journe_finite_product_holder_difference_g16`.
Source: de la Llave–Obaya (1999), Proposition 4.2, printed pp.168–169;
Journé (1988), pp.189–190, the small-factor product expansion.
The released G16 proof is retained. All bounds include derivatives of orders zero
through n and the order-n Hölder seminorm on the original open convex domain.
The list of factors may be empty or repeat indices, and δ may be zero.
-/

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

/-- Scalar product closure with the published full Hölder norm constant.

Source: de la Llave–Obaya (1999), Proposition 4.2, printed pp.168–169.
Apply the bilinear full Hölder estimate to scalar multiplication and use its
operator norm bound by one. Nonnegative factor bounds preserve the inequality. -/
theorem scalar_mul_holder_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ} {α A B : ℝ} {S : Set E} (hS : IsOpen S) (hconv : Convex ℝ S)
    (hα : 0 < α) (hα1 : α < 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {f g : E → ℝ} (hf : HasFiniteHolderBounds n α A f S)
    (hg : HasFiniteHolderBounds n α B g S) :
    HasFiniteHolderBounds n α ((2:ℝ)^(2*n+1)*A*B) (fun x ↦ f x*g x) S := by
  have H := deLaLlaveObaya_bilinear_holder_bound S hS hconv n α A B hα hα1 hA hB
    f g hf.1 hg.1 hf.2.1 hg.2.1 hf.2.2 hg.2.2 (ContinuousLinearMap.mul ℝ ℝ)
  apply HasFiniteHolderBounds.mono_bound H
  have hm := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  have hQ : 0 ≤ (2:ℝ)^(2*n+1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm hQ) (mul_nonneg hA hB)]

/-- The product of m scalar functions with full norm at most M≥1 has full
norm at most (Q M)^m, Q=2^(2n+1).

Source: de la Llave–Obaya (1999), Proposition 4.2, iterated; Journé (1988), pp.189–190.
Induct on the list. The empty product is constant one with full bound one.
At a new factor, bilinear closure multiplies the previous bound by Q M.
The list representation deliberately permits repeated coordinate factors. -/
theorem finite_product_holder_bound
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ} (hn : 1 ≤ n) {α M : ℝ} {S : Set E}
    (hS : IsOpen S) (hconv : Convex ℝ S) (hα : 0 < α) (hα1 : α < 1) (hM : 1 ≤ M)
    (f : ι → E → ℝ) (l : List ι)
    (hf : ∀ i ∈ l, HasFiniteHolderBounds n α M (f i) S) :
    HasFiniteHolderBounds n α (((2:ℝ)^(2*n+1)*M)^l.length)
      (fun x ↦ (l.map (fun i ↦ f i x)).prod) S := by
  induction l with
  | nil => simpa using finiteHolderBounds_const n hn α S (1:ℝ)
  | cons i l ih =>
    have ht := ih (fun j hj ↦ hf j (List.mem_cons_of_mem _ hj))
    have hi := hf i (List.mem_cons_self ..)
    have H := scalar_mul_holder_bound hS hconv hα hα1 (by linarith) (by positivity) hi ht
    simpa only [List.length_cons,List.map_cons,List.prod_cons,pow_succ,mul_comm] using H

/-- Finite products are Lipschitz in the full C^{n,α} norm on bounded sets.
Expand the new first factor difference, keeping the remaining product; the
second term is the old first factor times the remaining product difference.
Product closure and induction give m(QM)^m δ. This is the small-factor
algebra used for Journé's mixed monomials, with arbitrary repeated factors.

Source: de la Llave–Obaya (1999), Proposition 4.2; Journé (1988), pp.189–190.
The empty difference is constant zero. For a new factor, write the difference
as (fᵢ-gᵢ) times the f-tail product plus gᵢ times the tail difference. Their full
bounds are Q δ (Q M)^m and Q M m (Q M)^m δ. Since M≥1, Q≤Q M, so their sum is
at most (m+1)(Q M)^(m+1) δ. No factor is divided out, covering δ=0 and zero factors. -/
theorem finite_product_difference_holder_bound
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ} (hn : 1 ≤ n) {α M δ : ℝ} {S : Set E}
    (hS : IsOpen S) (hconv : Convex ℝ S) (hα : 0 < α) (hα1 : α < 1)
    (hM : 1 ≤ M) (hδ : 0 ≤ δ) (f g : ι → E → ℝ) (l : List ι)
    (hf : ∀ i ∈ l, HasFiniteHolderBounds n α M (f i) S)
    (hg : ∀ i ∈ l, HasFiniteHolderBounds n α M (g i) S)
    (hd : ∀ i ∈ l, HasFiniteHolderBounds n α δ (fun x ↦ f i x-g i x) S) :
    HasFiniteHolderBounds n α ((l.length:ℝ)*((2:ℝ)^(2*n+1)*M)^l.length*δ)
      (fun x ↦ (l.map (fun i ↦ f i x)).prod - (l.map (fun i ↦ g i x)).prod) S := by
  let Q : ℝ := 2^(2*n+1)
  have hQ : 0 ≤ Q := by positivity
  have hM0 : 0 ≤ M := by linarith
  induction l with
  | nil => simpa using finiteHolderBounds_const n hn α S (0:ℝ)
  | cons i l ih =>
    have htl := finite_product_holder_bound hn hS hconv hα hα1 hM f l
      (fun j hj ↦ hf j (List.mem_cons_of_mem _ hj))
    have htd := ih (fun j hj ↦ hf j (List.mem_cons_of_mem _ hj))
      (fun j hj ↦ hg j (List.mem_cons_of_mem _ hj))
      (fun j hj ↦ hd j (List.mem_cons_of_mem _ hj))
    have hfirst := scalar_mul_holder_bound hS hconv hα hα1 hδ (by positivity)
      (hd i (List.mem_cons_self ..)) htl
    have hsecond := scalar_mul_holder_bound hS hconv hα hα1 hM0 (by positivity)
      (hg i (List.mem_cons_self ..)) htd
    have hsum := hfirst.add hS hsecond
    have hbound : Q*δ*(Q*M)^l.length + Q*M*((l.length:ℝ)*(Q*M)^l.length*δ) ≤
        ((l.length+1:ℕ):ℝ)*(Q*M)^(l.length+1)*δ := by
      rw [Nat.cast_add,Nat.cast_one,pow_succ]
      have hle : Q ≤ Q*M := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hle (mul_nonneg (pow_nonneg (mul_nonneg hQ hM0) l.length) hδ)]
    have H := hsum.mono_bound hbound
    convert H using 1
    simp only [List.map_cons, List.prod_cons]
    funext x
    ring

/-- The highest Hölder seminorm of a finite scalar linear combination is
bounded by the sum of the absolute weighted seminorms. This uses actual
Fréchet derivatives on the open domain.

Source: Journé (1988), pp.189–190, finite polynomial expansion; linear derivative rules.
Differentiate each finite summand, commute constant scalar multiplication with the
iterated derivative, subtract at the two points, and apply the norm triangle inequality.
Each summand is bounded by |cᵢ| Kᵢ times the common distance power. Summing gives the claim. -/
theorem finite_weighted_sum_top_holder_bound
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {α : ℝ} {S : Set E} (hS : IsOpen S)
    (s : Finset ι) (f : ι → E → F) (c K : ι → ℝ)
    (hf : ∀ i ∈ s, ContDiffOn ℝ n (f i) S)
    (hK : ∀ i ∈ s, ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n (f i) x-iteratedFDeriv ℝ n (f i) y‖ ≤ K i*‖x-y‖^α) :
    ContDiffOn ℝ n (fun x ↦ ∑ i ∈ s, c i • f i x) S ∧
      ∀ x ∈ S, ∀ y ∈ S,
        ‖iteratedFDeriv ℝ n (fun x ↦ ∑ i ∈ s, c i • f i x) x-
          iteratedFDeriv ℝ n (fun x ↦ ∑ i ∈ s, c i • f i x) y‖ ≤
          (∑ i ∈ s, |c i| *K i)*‖x-y‖^α := by
  classical
  refine ⟨ContDiffOn.sum (fun i hi ↦ (hf i hi).const_smul (c i)),?_⟩
  intro x hx y hy
  have he (z : E) (hz : z ∈ S) :
      iteratedFDeriv ℝ n (fun x ↦ ∑ i ∈ s, c i • f i x) z =
        ∑ i ∈ s, c i • iteratedFDeriv ℝ n (f i) z := by
    rw [iteratedFDeriv_fun_sum_apply (fun i hi ↦
      ((hf i hi).contDiffAt (hS.mem_nhds hz)).const_smul (c i))]
    apply Finset.sum_congr rfl
    intro i hi
    exact iteratedFDeriv_const_smul_apply' ((hf i hi).contDiffAt (hS.mem_nhds hz))
  rw [he x hx,he y hy,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, ‖c i • iteratedFDeriv ℝ n (f i) x-
        c i • iteratedFDeriv ℝ n (f i) y‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, |c i| *(K i*‖x-y‖^α) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← smul_sub,norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hK i hi x hx y hy) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring

end HolomorphicAnosov.JourneLeafPolynomialApproximation
