import HolomorphicAnosov.Analysis.FDerivHolderBound
import HolomorphicAnosov.Analysis.BilinearHolderBound
import HolomorphicAnosov.Analysis.LowerJetHolderBound
import HolomorphicAnosov.Analysis.CompositionHolderFirstDerivative
import HolomorphicAnosov.Analysis.CompositionHolderPowerEstimate

set_option synthInstance.maxSize 512

namespace HolomorphicAnosov
open Filter
open scoped Topology _root_.Topology
universe u v

/-- DDLO Theorem 4.3(ii.3), pp.169–170, with receiving and output spaces in
one universe so the output can be replaced by its operator space in induction.

For order one the chain rule and the first-derivative Hölder estimate give the
bound, with numerical factor 4. At successor order k+1, apply induction to f
and Dg with bounds 2Af and Ag. The lower-jet downgrade supplies 2Af, while
right currying transfers the bound Ag to Dg and Af to Df. The bilinear Hölder
bound for operator composition then controls D(g∘f). The local chain rule and
right currying transfer its jet and Hölder bounds back to g∘f; its values are
bounded by Ag. Finally the numerical power estimate absorbs
Af(1+(2Af)^(k+α)) into (1+2^(k+α))(1+Af^(k+1+α)). -/
theorem composition_holder_bound_same_universe (n : ℕ) (α : ℝ) (hn : 1 ≤ n)
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ (E : Type u) (F G : Type v)
        [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
        [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
        [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
        (A : Set E) (B : Set F) (f : E → F) (g : F → G) (Af Ag : ℝ),
        IsOpen A → Convex ℝ A → IsOpen B → Convex ℝ B →
        ContDiffOn ℝ n f A → ContDiffOn ℝ n g B → Set.MapsTo f A B →
        0 ≤ Af → 0 ≤ Ag →
        (∀ j : ℕ, j ≤ n → ∀ x ∈ A, ‖iteratedFDeriv ℝ j f x‖ ≤ Af) →
        (∀ j : ℕ, j ≤ n → ∀ y ∈ B, ‖iteratedFDeriv ℝ j g y‖ ≤ Ag) →
        (∀ x ∈ A, ∀ y ∈ A,
          ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n f y‖ ≤ Af * ‖x - y‖ ^ α) →
        (∀ x ∈ B, ∀ y ∈ B,
          ‖iteratedFDeriv ℝ n g x - iteratedFDeriv ℝ n g y‖ ≤ Ag * ‖x - y‖ ^ α) →
        ContDiffOn ℝ n (g ∘ f) A ∧
          (∀ j : ℕ, j ≤ n → ∀ x ∈ A,
            ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤ M * Ag * (1 + Af ^ ((n : ℝ) + α))) ∧
          (∀ x ∈ A, ∀ y ∈ A,
            ‖iteratedFDeriv ℝ n (g ∘ f) x - iteratedFDeriv ℝ n (g ∘ f) y‖ ≤
              M * Ag * (1 + Af ^ ((n : ℝ) + α)) * ‖x - y‖ ^ α) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      refine ⟨4, by norm_num, ?_⟩
      intro E F G _ _ _ _ _ _ _ _ _ A B f g Af Ag hA hcA hB hcB hf hg hm hAf hAg hfn hgn hfh hgh
      have hfd (x : E) (hx : x ∈ A) : ‖fderiv ℝ f x‖ ≤ Af := by
        simpa only [norm_iteratedFDeriv_one] using hfn 1 le_rfl x hx
      have hgd (x : F) (hx : x ∈ B) : ‖fderiv ℝ g x‖ ≤ Ag := by
        simpa only [norm_iteratedFDeriv_one] using hgn 1 le_rfl x hx
      have hdiff (x : E) (hx : x ∈ A) (y : E) (hy : y ∈ A) :
          ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ Af * ‖x-y‖ ^ α := by
        have h := hfh x hx y hy
        rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right] at h
        simpa only [Function.comp_apply, ← LinearIsometryEquiv.map_sub,
          LinearIsometryEquiv.norm_map, iteratedFDeriv_zero_eq_comp] using h
      have hdiffg (x : F) (hx : x ∈ B) (y : F) (hy : y ∈ B) :
          ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ Ag * ‖x-y‖ ^ α := by
        have h := hgh x hx y hy
        rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right] at h
        simpa only [Function.comp_apply, ← LinearIsometryEquiv.map_sub,
          LinearIsometryEquiv.norm_map, iteratedFDeriv_zero_eq_comp] using h
      have hnum : Af * (1 + Af ^ α) ≤ 2 * (1 + Af ^ (1 + α)) := by
        simpa only [one_mul, Real.one_rpow, add_comm α 1, one_add_one_eq_two] using
          composition_holder_power_estimate Af 1 α hAf (by norm_num) hα.le
      have hp : 0 ≤ Af ^ (1 + α) := Real.rpow_nonneg hAf _
      refine ⟨hg.comp hf hm, ?_, ?_⟩
      · intro j hj x hx
        have hj' : j = 0 ∨ j = 1 := by omega
        rcases hj' with rfl | rfl
        · simp only [norm_iteratedFDeriv_zero, Function.comp_apply]
          have hb : ‖g (f x)‖ ≤ Ag := by
            simpa only [norm_iteratedFDeriv_zero] using hgn 0 (by omega) (f x) (hm hx)
          norm_num only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add]
          nlinarith [mul_nonneg hAg hp]
        · rw [norm_iteratedFDeriv_one,
            fderiv_comp x ((hg.contDiffAt (hB.mem_nhds (hm hx))).differentiableAt (by norm_num))
              ((hf.contDiffAt (hA.mem_nhds hx)).differentiableAt (by norm_num))]
          have hb := (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul (hgd (f x) (hm hx)) (hfd x hx) (norm_nonneg _) hAg)
          have hbase : Af ≤ 2 * (1 + Af ^ (1 + α)) := by
            nlinarith [Real.rpow_nonneg hAf α]
          norm_num only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add]
          nlinarith [mul_le_mul_of_nonneg_left hbase hAg, mul_nonneg hAg hp]
      · intro x hx y hy
        rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
        simp only [Function.comp_apply, ← LinearIsometryEquiv.map_sub,
          LinearIsometryEquiv.norm_map, iteratedFDeriv_zero_eq_comp]
        have hh := composition_fderiv_holder_bound A B hA hcA hB f g hf hg hm Af Ag α hAf hAg hα
          hfd hgd hdiff hdiffg x hx y hy
        have hr : 0 ≤ ‖x-y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
        apply hh.trans
        calc
          _ ≤ (2 * Ag * (1 + Af ^ (1 + α))) * ‖x-y‖ ^ α := by
            apply mul_le_mul_of_nonneg_right _ hr
            nlinarith [mul_le_mul_of_nonneg_left hnum hAg]
          _ ≤ _ := by
            norm_num only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add]
            have hhpos : 0 ≤ Ag * (1 + Af ^ (1 + α)) * ‖x-y‖ ^ α := by positivity
            nlinarith
    · obtain ⟨M, hM, ih⟩ := ih (by omega)
      let Q : ℝ := 2 ^ (2 * n + 1)
      let C : ℝ := Q * M * (1 + 2 ^ ((n : ℝ) + α))
      refine ⟨max 1 C, le_max_left _ _, ?_⟩
      intro E F G _ _ _ _ _ _ _ _ _ A B f g Af Ag hA hcA hB hcB hf hg hm hAf hAg hfn hgn hfh hgh
      obtain ⟨hfd, hfdn, hfdh⟩ := fderiv_holder_bound A hA n f hf Af α hfn hfh
      obtain ⟨hgd, hgdn, hgdh⟩ := fderiv_holder_bound B hB n g hg Ag α hgn hgh
      have hflow (x : E) (hx : x ∈ A) (y : E) (hy : y ∈ A) :
          ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n f y‖ ≤ (2 * Af) * ‖x-y‖ ^ α := by
        have h := lower_jet_holder_bound A hA hcA (n+1) α Af hα hα1.le hAf f hf
          (fun j hj z hz ↦ by rw [iteratedFDerivWithin_of_isOpen _ hA hz]; exact hfn j hj z hz)
          n (by omega) x hx y hy
        simpa only [iteratedFDerivWithin_of_isOpen _ hA hx,
          iteratedFDerivWithin_of_isOpen _ hA hy] using h
      obtain ⟨hR, hRn, hRh⟩ := ih E F (F →L[ℝ] G) A B f (fderiv ℝ g) (2*Af) Ag
        hA hcA hB hcB (hf.of_le (by exact_mod_cast Nat.le_succ n)) hgd hm
        (by positivity) hAg (fun j hj x hx ↦ (hfn j (by omega) x hx).trans (by linarith))
        hgdn hflow hgdh
      let Dg : E → F →L[ℝ] G := fderiv ℝ g ∘ f
      let Df : E → E →L[ℝ] F := fderiv ℝ f
      let R : E → E →L[ℝ] G := fun x ↦ (Dg x).comp (Df x)
      let K : ℝ := M * Ag * (1 + (2*Af) ^ ((n:ℝ)+α))
      have hK : 0 ≤ K := by dsimp [K]; positivity
      obtain ⟨hprod, hprodn, hprodh⟩ := deLaLlaveObaya_bilinear_holder_bound A hA hcA n α K Af
        hα hα1 hK hAf Dg Df hR hfd hRn hfdn hRh hfdh
        (ContinuousLinearMap.compL ℝ E F G)
      have hchain : Set.EqOn (fderiv ℝ (g ∘ f)) R A := by
        intro x hx
        exact fderiv_comp x ((hg.contDiffAt (hB.mem_nhds (hm hx))).differentiableAt (by positivity))
          ((hf.contDiffAt (hA.mem_nhds hx)).differentiableAt (by positivity))
      have heq (j : ℕ) (x : E) (hx : x ∈ A) :
          iteratedFDeriv ℝ j (fderiv ℝ (g ∘ f)) x = iteratedFDeriv ℝ j R x := by
        have he : fderiv ℝ (g ∘ f) =ᶠ[𝓝 x] R := by
          filter_upwards [hA.mem_nhds hx] with z hz using hchain hz
        exact (he.iteratedFDeriv ℝ j).eq_of_nhds
      have hQ : 0 ≤ Q := by dsimp [Q]; positivity
      have hnum0 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_compL_le ℝ E F G) hQ) hK) hAf
      have hnum := hnum0.trans (show Q * 1 * K * Af ≤
          max 1 C * Ag * (1 + Af ^ ((n+1:ℕ) + α)) from by
        have hQ : 0 ≤ Q := by dsimp [Q]; positivity
        have hM0 : 0 ≤ M := by linarith
        have hpow := composition_holder_power_estimate Af 2 ((n:ℝ)+α) hAf (by norm_num)
          (by positivity)
        have hpow' : Af * (1 + (2*Af)^((n:ℝ)+α)) ≤
            (1+2^((n:ℝ)+α)) * (1+Af^((n+1:ℕ)+α)) := by
          have he : ((n + 1 : ℕ) : ℝ) + α = ((n : ℝ) + α) + 1 := by push_cast; ring
          rw [he]
          exact hpow
        calc
          _ = (Q*M*Ag) * (Af * (1+(2*Af)^((n:ℝ)+α))) := by dsimp [K]; ring
          _ ≤ (Q*M*Ag) * ((1+2^((n:ℝ)+α)) * (1+Af^((n+1:ℕ)+α))) :=
            mul_le_mul_of_nonneg_left hpow' (by positivity)
          _ = C * Ag * (1+Af^((n+1:ℕ)+α)) := by dsimp [C]; ring
          _ ≤ _ := by gcongr; exact le_max_right 1 C)
      refine ⟨hg.comp hf hm, ?_, ?_⟩
      · intro j hj x hx
        cases j with
        | zero =>
          simp only [norm_iteratedFDeriv_zero, Function.comp_apply]
          have hv : ‖g (f x)‖ ≤ Ag := by
            simpa only [norm_iteratedFDeriv_zero] using hgn 0 (by omega) (f x) (hm hx)
          apply hv.trans
          have hmax : 1 ≤ max 1 C := le_max_left _ _
          have hp : 0 ≤ Af ^ ((n+1:ℕ)+α) := Real.rpow_nonneg hAf _
          nlinarith [mul_nonneg hAg hp, mul_le_mul_of_nonneg_right hmax hAg]
        | succ j =>
          rw [iteratedFDeriv_succ_eq_comp_right]
          simp only [Function.comp_apply, LinearIsometryEquiv.norm_map]
          rw [heq j x hx]
          exact (hprodn j (by omega) x hx).trans hnum
      · intro x hx y hy
        rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
        simp only [Function.comp_apply, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
        rw [heq n x hx, heq n y hy]
        exact (hprodh x hx y hy).trans
          (mul_le_mul_of_nonneg_right hnum (Real.rpow_nonneg (norm_nonneg _) _))

end HolomorphicAnosov

