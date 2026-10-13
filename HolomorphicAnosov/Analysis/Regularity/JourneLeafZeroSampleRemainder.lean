import HolomorphicAnosov.Analysis.Regularity.JourneAffineLineJets
import HolomorphicAnosov.Analysis.Regularity.JourneMultilinearJetPolynomial
import Mathlib.Tactic


noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

/-- Hölder control of the highest spatial derivative gives the exact scaled highest line-jet estimate K ||v||^(n+α). -/
theorem top_holder_affine_line_jets_g18 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} (hS : IsOpen S) {n : ℕ} {α K : ℝ} (hα : 0 ≤ α) (hK : 0 ≤ K)
    {f : E → F} (hf : ContDiffOn ℝ n f S)
    (hholder : ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n f x-iteratedFDeriv ℝ n f y‖ ≤ K*‖x-y‖^α) (a v : E)
    (hline : ∀ t ∈ Icc (0:ℝ) 1, a+t•v ∈ S) :
    ContDiffOn ℝ n (fun t : ℝ ↦ f (a+t•v)) (Icc 0 1) ∧
      (∀ j : ℕ, j ≤ n →
        iteratedDerivWithin j (fun t : ℝ ↦ f (a+t•v)) (Icc 0 1) 0 =
          iteratedFDeriv ℝ j f a (fun _ ↦ v)) ∧
      ∀ t ∈ Icc (0:ℝ) 1,
        ‖iteratedDerivWithin n (fun t : ℝ ↦ f (a+t•v)) (Icc 0 1) t -
          iteratedFDeriv ℝ n f a (fun _ ↦ v)‖ ≤ K * ‖v‖ ^ ((n:ℝ)+α) := by
  obtain ⟨hsmooth, hjets⟩ := affine_line_jets hS hf a v hline
  have ha : a ∈ S := by simpa using hline 0 (by constructor <;> norm_num)
  refine ⟨hsmooth, ?_, ?_⟩
  · intro j hj
    simpa using hjets j hj 0 (by constructor <;> norm_num)
  · intro t ht
    rw [hjets n le_rfl t ht]
    have hdist : ‖a+t•v-a‖ ≤ ‖v‖ := by
      simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        using mul_le_of_le_one_left (norm_nonneg v) ht.2
    have hb := (hholder (a+t•v) (hline t ht) a ha).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hdist hα) hK)
    have heval := (iteratedFDeriv ℝ n f (a+t•v) - iteratedFDeriv ℝ n f a).le_opNorm
      (fun _ ↦ v)
    simp only [sub_apply, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin] at heval
    calc
      _ ≤ ‖iteratedFDeriv ℝ n f (a+t•v) - iteratedFDeriv ℝ n f a‖ * ‖v‖^n := heval
      _ ≤ (K * ‖v‖^α) * ‖v‖^n := mul_le_mul_of_nonneg_right hb (pow_nonneg (norm_nonneg _) _)
      _ = K * ‖v‖^((n:ℝ)+α) := by
        rw [Real.rpow_add_of_nonneg (norm_nonneg _) (Nat.cast_nonneg n) hα, Real.rpow_natCast]
        ring

/-- The degree-n Taylor polynomial of a scalar C^{n,α} function has remainder at most K ||v||^(n+α) along any segment in its open domain. -/
theorem top_holder_taylor_remainder_g18 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : IsOpen S) {n : ℕ} (hn : 1 ≤ n)
    {α K : ℝ} (hα : 0 ≤ α) (hK : 0 ≤ K) {f : E → ℝ}
    (hf : ContDiffOn ℝ n f S)
    (hholder : ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n f x-iteratedFDeriv ℝ n f y‖ ≤ K*‖x-y‖^α) (a v : E)
    (hline : ∀ t ∈ Icc (0:ℝ) 1, a+t•v ∈ S) :
    |f (a+v) - ∑ j : Fin (n+1), (j.val.factorial:ℝ)⁻¹ *
      iteratedFDeriv ℝ j.val f a (fun _ ↦ v)| ≤ K * ‖v‖^((n:ℝ)+α) := by
  let T : (j : Fin (n+1)) → ContinuousMultilinearMap ℝ (fun _ : Fin j.val ↦ E) ℝ :=
    fun j ↦ iteratedFDeriv ℝ j.val f a
  let Q : ℝ → ℝ := fun t ↦ ∑ j : Fin (n+1), (j.val.factorial:ℝ)⁻¹ * T j (fun _ ↦ t•v)
  let g : ℝ → ℝ := fun t ↦ f (a+t•v)
  let R : ℝ → ℝ := g-Q
  obtain ⟨hQ,hQzero,hQtop⟩ := multilinear_jet_line_derivatives T v
  obtain ⟨hg,hgzero,hgtop⟩ := top_holder_affine_line_jets_g18 hS hα hK hf hholder a v hline
  have huniq : UniqueDiffOn ℝ (Icc (0:ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hR : ContDiffOn ℝ n R (Icc 0 1) := hg.sub (hQ.contDiffOn.of_le (by simp))
  have hRD (j : ℕ) (hj : j ≤ n) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      iteratedDerivWithin j R (Icc 0 1) t =
        iteratedDerivWithin j g (Icc 0 1) t - iteratedDeriv j Q t := by
    change iteratedDerivWithin j (g-Q) (Icc 0 1) t = _
    rw [iteratedDerivWithin_sub ht huniq
      ((hg t ht).of_le (by exact_mod_cast hj))
      (hQ.contDiffAt.contDiffWithinAt.of_le (by simp)),
      iteratedDerivWithin_eq_iteratedDeriv huniq (hQ.contDiffAt.of_le (by simp)) ht]
  have hzero (j : ℕ) (hj : j < n) : iteratedDerivWithin j R (Icc 0 1) 0 = 0 := by
    rw [hRD j hj.le 0 (by constructor <;> norm_num), hgzero j hj.le,
      hQzero ⟨j,Nat.lt_trans hj (Nat.lt_succ_self n)⟩]
    exact sub_self _
  have hbound (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖iteratedDerivWithin n R (Icc 0 1) t‖ ≤ K * ‖v‖^((n:ℝ)+α) := by
    rw [hRD n le_rfl t ht, hQtop]
    exact hgtop t ht
  have horder : n-1+1=n := Nat.sub_add_cancel hn
  have hTaylor : taylorWithinEval R (n-1) (Icc 0 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro j hj
    rw [hzero j (by simpa [horder] using Finset.mem_range.mp hj), smul_zero]
  have hR' : ContDiffOn ℝ ((n-1:ℕ)+1) R (Icc 0 1) := by
    convert hR using 1
    norm_cast
  have hb := taylor_mean_remainder_bound (f:=R) (n:=n-1)
    (a:=0) (b:=1) (x:=1) (C:=K * ‖v‖^((n:ℝ)+α)) zero_le_one hR'
    (by constructor <;> norm_num) (by simpa only [horder] using hbound)
  have hfact : (1:ℝ) ≤ ((n-1).factorial:ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (n-1))
  have hb' : |R 1| ≤ K * ‖v‖^((n:ℝ)+α) / ((n-1).factorial:ℝ) := by
    simpa only [hTaylor, sub_zero, one_pow, mul_one, Real.norm_eq_abs] using hb
  have hb'' := hb'.trans (div_le_self
    (mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _)) hfact)
  simpa only [R, Pi.sub_apply, g, Q, one_smul, T] using hb''



/-- Journé (1988), p.190, equation (4), in any Euclidean block dimension, including nonzero sample residuals. (Journé, 1988) -/
theorem leaf_sample_remainder {d n : ℕ} {ι : Type*} (hn : 1 ≤ n)
    {S : Set (Block d)} (hS : IsOpen S) (hconv : Convex ℝ S) (hzero : (0:Block d) ∈ S)
    {α K : ℝ} (hα : 0 ≤ α) (hK : 0 ≤ K) (f : Block d → ℝ)
    (hf : ContDiffOn ℝ n f S)
    (hholder : ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n f x-iteratedFDeriv ℝ n f y‖ ≤ K*‖x-y‖^α)
    (a : ι → Block d) (y : Block d)
    (R L : ℝ) (hR : 0 ≤ R) (_hL : 0 ≤ L)
    (ha : ∀ i, a i ∈ S) (hay : y ∈ S)
    (hanorm : ∀ i, ‖a i‖ ≤ R) (hynorm : ‖y‖ ≤ R)
    (M : ℝ) (hM : 0 ≤ M) (hsamples : ∀ i, |f (a i)| ≤ M)
    (hinterp : ∀ P : MvPolynomial (Fin d) ℝ, P.totalDegree ≤ n →
      ∀ M : ℝ, 0 ≤ M → (∀ i, |MvPolynomial.eval (fun j ↦ a i j) P| ≤ M) →
        |MvPolynomial.eval (fun j ↦ y j) P| ≤ L*M) :
    |f y| ≤ L*M+(L+1)*K*R^((n:ℝ)+α) := by
  let T : (j : Fin (n+1)) → ContinuousMultilinearMap ℝ (fun _ : Fin j.val ↦ Block d) ℝ :=
    fun j ↦ iteratedFDeriv ℝ j.val f 0
  obtain ⟨P,hP,hPeval⟩ := multilinear_jet_polynomial_exists (0:Block d) T
  have herror (z : Block d) (hz : z ∈ S) (hzn : ‖z‖ ≤ R) :
      |f z - MvPolynomial.eval (fun i ↦ z i) P| ≤ K*R^((n:ℝ)+α) := by
    have he := top_holder_taylor_remainder_g18 hS hn hα hK hf hholder 0 z
      (fun t ht ↦ hconv.add_smul_mem hzero (by simpa using hz) ht)
    rw [hPeval]
    simp only [zero_add, sub_zero] at he ⊢
    exact he.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hzn (by positivity)) hK)
  have hsamplebound : ∀ i, |MvPolynomial.eval (fun j ↦ a i j) P| ≤ M+K*R^((n:ℝ)+α) := by
    intro i
    have hb := herror (a i) (ha i) (hanorm i)
    have htri := abs_sub_le (MvPolynomial.eval (fun j ↦ a i j) P) (f (a i)) 0
    rw [abs_sub_comm (MvPolynomial.eval (fun j ↦ a i j) P) (f (a i))] at htri
    simp only [sub_zero] at htri
    linarith [hsamples i]
  have hpoly := hinterp P hP (M+K*R^((n:ℝ)+α)) (by positivity) hsamplebound
  have he := herror y hay hynorm
  calc
    |f y| ≤ |f y - MvPolynomial.eval (fun i ↦ y i) P| +
        |MvPolynomial.eval (fun i ↦ y i) P| := by
      simpa only [sub_zero] using abs_sub_le (f y) (MvPolynomial.eval (fun i ↦ y i) P) 0
    _ ≤ K*R^((n:ℝ)+α) + L*(M+K*R^((n:ℝ)+α)) := add_le_add he hpoly
    _ = _ := by ring

/-- The zero-sample specialization, retaining the earlier full-bound interface. -/
theorem leaf_zero_sample_remainder {d n : ℕ} {ι : Type*} (hn : 1 ≤ n)
    {S : Set (Block d)} (hS : IsOpen S) (hconv : Convex ℝ S) (hzero : (0:Block d) ∈ S)
    {α K : ℝ} (hα : 0 ≤ α) (hK : 0 ≤ K) (f : Block d → ℝ)
    (hf : HasFiniteHolderBounds n α K f S) (a : ι → Block d) (y : Block d)
    (R L : ℝ) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (ha : ∀ i, a i ∈ S) (hay : y ∈ S)
    (hanorm : ∀ i, ‖a i‖ ≤ R) (hynorm : ‖y‖ ≤ R)
    (hsamples : ∀ i, f (a i) = 0)
    (hinterp : ∀ P : MvPolynomial (Fin d) ℝ, P.totalDegree ≤ n →
      ∀ M : ℝ, 0 ≤ M → (∀ i, |MvPolynomial.eval (fun j ↦ a i j) P| ≤ M) →
        |MvPolynomial.eval (fun j ↦ y j) P| ≤ L*M) :
    |f y| ≤ (L+1)*K*R^((n:ℝ)+α) := by
  simpa only [mul_zero,zero_add] using leaf_sample_remainder hn hS hconv hzero hα hK f
    hf.1 hf.2.2 a y R L hR hL ha hay hanorm hynorm 0 le_rfl
    (fun i ↦ by rw [hsamples i,abs_zero]) hinterp

end HolomorphicAnosov.JourneLeafPolynomialApproximation
