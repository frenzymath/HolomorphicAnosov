import HolomorphicAnosov.Analysis.Regularity.GraphFoliationData
import HolomorphicAnosov.Analysis.Regularity.JourneMultilinearJetLineDerivatives
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

/-- Restricting a C^n function to an affine line evaluates its jth derivative
on j copies of the line direction. This follows by composing its finite Taylor
series with the continuous affine line map, restricting the resulting series
to [0,1], and using uniqueness of finite Taylor coefficients there. The source
is open, so its within derivatives equal its ordinary derivatives. Endpoints
of the line and order zero are included. -/
theorem affine_line_jets {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} (hS : IsOpen S) {n : ℕ} {f : E → F}
    (hf : ContDiffOn ℝ n f S) (a v : E)
    (hline : ∀ t ∈ Icc (0:ℝ) 1, a + t • v ∈ S) :
    ContDiffOn ℝ n (fun t : ℝ ↦ f (a+t•v)) (Icc 0 1) ∧
      ∀ j : ℕ, j ≤ n → ∀ t ∈ Icc (0:ℝ) 1,
        iteratedDerivWithin j (fun t : ℝ ↦ f (a+t•v)) (Icc 0 1) t =
          iteratedFDeriv ℝ j f (a+t•v) (fun _ ↦ v) := by
  let l : ℝ →ᴬ[ℝ] E := ContinuousAffineMap.lineMap a (a+v)
  have hl (t : ℝ) : l t = a+t•v := by
    simp [l, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_module', add_comm]
  have hlin : l.contLinear (1:ℝ) = v := by
    change (AffineMap.lineMap (k := ℝ) a (a+v)).linear 1 = v
    simp [AffineMap.lineMap]
  have hmaps : MapsTo l (Icc 0 1) S := fun t ht ↦ by rw [hl]; exact hline t ht
  have hseries := ((hf.ftaylorSeriesWithin hS.uniqueDiffOn).comp_continuousAffineMap l).mono hmaps
  have heq : (f ∘ l) = (fun t : ℝ ↦ f (a+t•v)) := by funext t; simp [hl]
  refine ⟨?_, ?_⟩
  · rw [← heq]
    exact hseries.contDiffOn
  · intro j hj t ht
    rw [← heq, iteratedDerivWithin_eq_iteratedFDerivWithin,
      ← hseries.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hj)
        (uniqueDiffOn_Icc zero_lt_one) ht]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hlin,
      ftaylorSeriesWithin, hl]
    rw [iteratedFDerivWithin_of_isOpen j hS (hline t ht)]

/-- Hölder control of the highest spatial derivative gives the exact scaled
highest line-jet estimate K ||v||^(n+α). Apply the affine-line formula, the
multilinear operator norm estimate, and ||t v||≤||v|| for t∈[0,1]. -/
theorem holder_affine_line_jets {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} (hS : IsOpen S) {n : ℕ} {α K : ℝ} (hα : 0 ≤ α) (hK : 0 ≤ K)
    {f : E → F} (hf : HasFiniteHolderBounds n α K f S) (a v : E)
    (hline : ∀ t ∈ Icc (0:ℝ) 1, a+t•v ∈ S) :
    ContDiffOn ℝ n (fun t : ℝ ↦ f (a+t•v)) (Icc 0 1) ∧
      (∀ j : ℕ, j ≤ n →
        iteratedDerivWithin j (fun t : ℝ ↦ f (a+t•v)) (Icc 0 1) 0 =
          iteratedFDeriv ℝ j f a (fun _ ↦ v)) ∧
      ∀ t ∈ Icc (0:ℝ) 1,
        ‖iteratedDerivWithin n (fun t : ℝ ↦ f (a+t•v)) (Icc 0 1) t -
          iteratedFDeriv ℝ n f a (fun _ ↦ v)‖ ≤ K * ‖v‖ ^ ((n:ℝ)+α) := by
  obtain ⟨hsmooth, hjets⟩ := affine_line_jets hS hf.1 a v hline
  have ha : a ∈ S := by simpa using hline 0 (by constructor <;> norm_num)
  refine ⟨hsmooth, ?_, ?_⟩
  · intro j hj
    simpa using hjets j hj 0 (by constructor <;> norm_num)
  · intro t ht
    rw [hjets n le_rfl t ht]
    have hdist : ‖a+t•v-a‖ ≤ ‖v‖ := by
      simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        using mul_le_of_le_one_left (norm_nonneg v) ht.2
    have hb := (hf.2.2 (a+t•v) (hline t ht) a ha).trans
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

/-- The degree-n Taylor polynomial of a scalar C^{n,α} function has remainder
at most K ||v||^(n+α) along any segment in its open domain. Subtract the
factorial-weighted multilinear Taylor polynomial from the line restriction.
Its derivatives below n vanish at zero; its nth derivative has the preceding
Hölder bound. The scalar Taylor remainder theorem at order n-1 bounds the
residual at one by this constant divided by (n-1)!, hence by the constant. -/
theorem holder_taylor_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : IsOpen S) {n : ℕ} (hn : 1 ≤ n)
    {α K : ℝ} (hα : 0 ≤ α) (hK : 0 ≤ K) {f : E → ℝ}
    (hf : HasFiniteHolderBounds n α K f S) (a v : E)
    (hline : ∀ t ∈ Icc (0:ℝ) 1, a+t•v ∈ S) :
    |f (a+v) - ∑ j : Fin (n+1), (j.val.factorial:ℝ)⁻¹ *
      iteratedFDeriv ℝ j.val f a (fun _ ↦ v)| ≤ K * ‖v‖^((n:ℝ)+α) := by
  let T : (j : Fin (n+1)) → ContinuousMultilinearMap ℝ (fun _ : Fin j.val ↦ E) ℝ :=
    fun j ↦ iteratedFDeriv ℝ j.val f a
  let Q : ℝ → ℝ := fun t ↦ ∑ j : Fin (n+1), (j.val.factorial:ℝ)⁻¹ * T j (fun _ ↦ t•v)
  let g : ℝ → ℝ := fun t ↦ f (a+t•v)
  let R : ℝ → ℝ := g-Q
  obtain ⟨hQ,hQzero,hQtop⟩ := multilinear_jet_line_derivatives T v
  obtain ⟨hg,hgzero,hgtop⟩ := holder_affine_line_jets hS hα hK hf a v hline
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

end HolomorphicAnosov.JourneLeafPolynomialApproximation
