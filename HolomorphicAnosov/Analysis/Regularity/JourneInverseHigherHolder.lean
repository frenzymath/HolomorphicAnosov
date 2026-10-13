import HolomorphicAnosov.Analysis.Regularity.JourneOperatorInverseHolder
import HolomorphicAnosov.Analysis.CompositionHolderBound

noncomputable section
set_option synthInstance.maxSize 2048
namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- The uniform composition estimate, also at order zero when the inner map
has a separate Lipschitz bound. At zero use the outer Hölder modulus along
that Lipschitz map; at positive orders use the published composition estimate.
The constant precedes the domains and maps. -/
theorem composition_holder_bound_including_zero
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (n : ℕ) (α a b k : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hk : 0 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set E) (V : Set F),
      IsOpen U → Convex ℝ U → IsOpen V → Convex ℝ V →
      ∀ (f : E → F) (g : F → G), ContDiffOn ℝ n f U → ContDiffOn ℝ n g V →
      MapsTo f U V →
      (∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ ≤ k * ‖x - y‖) →
      (∀ j ≤ n, ∀ x ∈ U, ‖iteratedFDeriv ℝ j f x‖ ≤ b) →
      (∀ j ≤ n, ∀ x ∈ V, ‖iteratedFDeriv ℝ j g x‖ ≤ a) →
      (∀ x ∈ U, ∀ y ∈ U,
        ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n f y‖ ≤ b * ‖x - y‖ ^ α) →
      (∀ x ∈ V, ∀ y ∈ V,
        ‖iteratedFDeriv ℝ n g x - iteratedFDeriv ℝ n g y‖ ≤ a * ‖x - y‖ ^ α) →
      ContDiffOn ℝ n (g ∘ f) U ∧
      (∀ j ≤ n, ∀ x ∈ U, ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤ C) ∧
      (∀ x ∈ U, ∀ y ∈ U,
        ‖iteratedFDeriv ℝ n (g ∘ f) x - iteratedFDeriv ℝ n (g ∘ f) y‖ ≤
          C * ‖x - y‖ ^ α) := by
  by_cases hn : n = 0
  · subst n
    refine ⟨max a (a * k ^ α), le_max_of_le_left ha, ?_⟩
    intro U V hU hcU hV hcV f g hf hg hm hlip hfn hgn hfh hgh
    refine ⟨hg.comp hf hm, ?_, ?_⟩
    · intro j hj x hx
      have hj0 : j = 0 := by omega
      subst j
      simpa only [norm_iteratedFDeriv_zero, Function.comp_apply] using
        (hgn 0 le_rfl (f x) (hm hx)).trans (le_max_left _ _)
    · intro x hx y hy
      have h := hgh (f x) (hm hx) (f y) (hm hy)
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
        LinearIsometryEquiv.norm_map] at h ⊢
      calc
        _ ≤ a * ‖f x - f y‖ ^ α := h
        _ ≤ a * (k * ‖x - y‖) ^ α := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) (hlip x hx y hy) hα.le) ha
        _ = (a * k ^ α) * ‖x - y‖ ^ α := by
          rw [Real.mul_rpow hk (norm_nonneg _)]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg (norm_nonneg _) _)
  · obtain ⟨M, hM, H⟩ := composition_holder_bound n α (by omega) hα hα1
    refine ⟨M * a * (1 + b ^ ((n : ℝ) + α)), by positivity, ?_⟩
    intro U V hU hcU hV hcV f g hf hg hm hlip hfn hgn hfh hgh
    obtain ⟨hcont, hjets, hholder⟩ := H E F G U V f g b a hU hcU hV hcV hf hg hm hb ha
      (fun j hj x hx ↦ by simpa only [iteratedFDerivWithin_of_isOpen _ hU hx] using hfn j hj x hx)
      (fun j hj x hx ↦ by simpa only [iteratedFDerivWithin_of_isOpen _ hV hx] using hgn j hj x hx)
      (fun x hx y hy ↦ by simpa only [iteratedFDerivWithin_of_isOpen _ hU hx,
        iteratedFDerivWithin_of_isOpen _ hU hy] using hfh x hx y hy)
      (fun x hx y hy ↦ by simpa only [iteratedFDerivWithin_of_isOpen _ hV hx,
        iteratedFDerivWithin_of_isOpen _ hV hy] using hgh x hx y hy)
    refine ⟨hcont, ?_, ?_⟩
    · intro j hj x hx
      simpa only [iteratedFDerivWithin_of_isOpen _ hU hx] using hjets j hj x hx
    · intro x hx y hy
      simpa only [iteratedFDerivWithin_of_isOpen _ hU hx,
        iteratedFDerivWithin_of_isOpen _ hU hy] using hholder x hx y hy

/-- Uniform finite-order Hölder bounds for an existing smooth inverse on
specified open convex domains. The inverse has a common Lipschitz constant k
and value bound m; the forward map has a common C^{n,alpha} bound a. Then the
inverse has a C^{n,alpha} bound independent of the maps and domains.

Proof: order zero follows from the inverse Lipschitz and value bounds, splitting
at distance one. At order n+1, lower the forward bound to 2a and apply induction.
Compose Df with the order-n inverse using the uniform composition estimate.
Differentiate the actual inverse identities to show that Dg is its pointwise
operator inverse. Apply the inverse operator Hölder bound, whose constants
are chosen before the domain and fields, and transfer via right currying to
all positive-order jets of g. Values remain controlled by m. No new inverse,
receiving domain or parameter smoothness is asserted. -/
theorem inverse_function_holder_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) (α a k m : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ha : 0 ≤ a) (hk : 0 ≤ k) (hm : 0 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set E) (V : Set F),
      IsOpen U → Convex ℝ U → IsOpen V → Convex ℝ V →
      ∀ (f : E → F) (g : F → E), ContDiffOn ℝ n f U → ContDiffOn ℝ n g V →
      MapsTo g V U → (∀ x ∈ U, g (f x) = x) → (∀ y ∈ V, f (g y) = y) →
      (∀ x ∈ V, ∀ y ∈ V, ‖g x - g y‖ ≤ k * ‖x - y‖) →
      (∀ y ∈ V, ‖g y‖ ≤ m) →
      (∀ j ≤ n, ∀ x ∈ U, ‖iteratedFDeriv ℝ j f x‖ ≤ a) →
      (∀ x ∈ U, ∀ y ∈ U,
        ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n f y‖ ≤ a * ‖x - y‖ ^ α) →
      (∀ j ≤ n, ∀ x ∈ V, ‖iteratedFDeriv ℝ j g x‖ ≤ C) ∧
      (∀ x ∈ V, ∀ y ∈ V,
        ‖iteratedFDeriv ℝ n g x - iteratedFDeriv ℝ n g y‖ ≤ C * ‖x - y‖ ^ α) := by
  induction n generalizing a with
  | zero =>
    refine ⟨max m (max k (2 * m)), le_max_of_le_left hm, ?_⟩
    intro U V hU hcU hV hcV f g hf hg hmap hgf hfg hlip hgn hfn hfh
    constructor
    · intro j hj x hx
      have hj0 : j = 0 := by omega
      subst j
      simpa only [norm_iteratedFDeriv_zero] using (hgn x hx).trans (le_max_left _ _)
    · intro x hx y hy
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
        LinearIsometryEquiv.norm_map]
      by_cases hd : ‖x-y‖ ≤ 1
      · have hp : ‖x-y‖ ≤ ‖x-y‖ ^ α := by
          convert Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hd hα.le hα1.le using 1
          simp only [Real.rpow_one]
        exact (hlip x hx y hy).trans ((mul_le_mul_of_nonneg_left hp hk).trans
          (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _))
            (Real.rpow_nonneg (norm_nonneg _) _)))
      · have hp := Real.one_le_rpow (le_of_not_ge hd) hα.le
        calc
          _ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
          _ ≤ 2 * m := by linarith [hgn x hx, hgn y hy]
          _ ≤ (2 * m) * ‖x-y‖ ^ α := by nlinarith
          _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _))
            (Real.rpow_nonneg (norm_nonneg _) _)
  | succ n ih =>
    obtain ⟨b, hb, Hb⟩ := ih (2*a) (by positivity)
    obtain ⟨d, hd, Hd⟩ := composition_holder_bound_including_zero
      (E := F) (F := E) (G := E →L[ℝ] F) n α a b k hα hα1 ha hb hk
    obtain ⟨c, hc, Hc⟩ := inverse_operator_holder_bound
      (D := F) (E := E) (F := F) n α d k hα hα1 hd hk
    refine ⟨max m c, le_max_of_le_left hm, ?_⟩
    intro U V hU hcU hV hcV f g hf hg hmap hgf hfg hlip hgn hfn hfh
    have hfncont : ContDiffOn ℝ n f U := hf.of_le (by exact_mod_cast Nat.le_succ n)
    have hgncont : ContDiffOn ℝ n g V := hg.of_le (by exact_mod_cast Nat.le_succ n)
    have hflower : ∀ x ∈ U, ∀ y ∈ U,
        ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n f y‖ ≤ (2*a) * ‖x-y‖ ^ α := by
      intro x hx y hy
      have h := lower_jet_holder_bound U hU hcU (n+1) α a hα hα1.le ha f hf
        (fun j hj z hz ↦ by rw [iteratedFDerivWithin_of_isOpen _ hU hz]; exact hfn j hj z hz)
        n (Nat.lt_succ_self n) x hx y hy
      simpa only [iteratedFDerivWithin_of_isOpen _ hU hx,
        iteratedFDerivWithin_of_isOpen _ hU hy] using h
    obtain ⟨hgjets, hgholder⟩ := Hb U V hU hcU hV hcV f g hfncont hgncont hmap hgf hfg
      hlip hgn (fun j hj x hx ↦ (hfn j (by omega) x hx).trans (by linarith)) hflower
    obtain ⟨hDf, hDfjets, hDfholder⟩ := fderiv_holder_bound U hU n f hf a α hfn hfh
    obtain ⟨hA, hAjets, hAholder⟩ := Hd V U hV hcV hU hcU g (fderiv ℝ f) hgncont hDf
      hmap hlip hgjets hDfjets hgholder hDfholder
    have hDg : ContDiffOn ℝ n (fderiv ℝ g) V := hg.fderiv_of_isOpen hV (by simp)
    have hfD (x : E) (hx : x ∈ U) : DifferentiableAt ℝ f x :=
      (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hgD (y : F) (hy : y ∈ V) : DifferentiableAt ℝ g y :=
      (hg.contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp)
    have hAB (y : F) (hy : y ∈ V) :
        (fderiv ℝ f (g y)).comp (fderiv ℝ g y) = ContinuousLinearMap.id ℝ F := by
      have H := (hfD (g y) (hmap hy)).hasFDerivAt.comp y (hgD y hy).hasFDerivAt
      apply HasFDerivAt.unique _ (hasFDerivAt_id y)
      apply H.congr_of_eventuallyEq
      filter_upwards [hV.mem_nhds hy] with z hz using (hfg z hz).symm
    have hBA (y : F) (hy : y ∈ V) :
        (fderiv ℝ g y).comp (fderiv ℝ f (g y)) = ContinuousLinearMap.id ℝ E := by
      have H := (hgD y hy).hasFDerivAt
      rw [← hfg y hy] at H
      have H' := H.comp (g y) (hfD (g y) (hmap hy)).hasFDerivAt
      rw [hfg y hy] at H'
      apply HasFDerivAt.unique _ (hasFDerivAt_id (g y))
      apply H'.congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds (hmap hy)] with z hz using (hgf z hz).symm
    have hDgn (y : F) (hy : y ∈ V) : ‖fderiv ℝ g y‖ ≤ k :=
      norm_fderiv_le_of_lipschitzOn ℝ (hV.mem_nhds hy)
        (show LipschitzOnWith ⟨k,hk⟩ g V from lipschitzOnWith_iff_norm_sub_le.mpr hlip)
    obtain ⟨hBjets, hBholder⟩ := Hc V hV hcV (fderiv ℝ f ∘ g) (fderiv ℝ g)
      hA hDg hAB hBA hDgn hAjets hAholder
    constructor
    · intro j hj x hx
      cases j with
      | zero => simpa only [norm_iteratedFDeriv_zero] using (hgn x hx).trans (le_max_left _ _)
      | succ j =>
        rw [← norm_iteratedFDeriv_fderiv]
        exact (hBjets j (by omega) x hx).trans (le_max_right _ _)
    · intro x hx y hy
      rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
      simp only [Function.comp_apply, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
      exact (hBholder x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (norm_nonneg _) _))

end HolomorphicAnosov
