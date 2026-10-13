import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

open scoped ContDiff ZeroAtInfty

namespace HolomorphicAnosov.Analysis

/-- The derivative coordinates of a smooth weighted composition map.
Source: Wells (1976), p.288, equation (1). Evaluation at coordinate `n` is bounded
linear. Apply the iterated chain rule to the equality between evaluation after `C`
and the composition of `f` with the scaled evaluation map. Move the input scalars
through the multilinear derivative and combine them with the output scalar.
The assumed smoothness of `C` is used here; this lemma does not establish it. -/
theorem weighted_c0_derivative_formula
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s lam : ℝ) (r : ℕ∞) (f : E → F) (C : C₀(ℕ, E) → C₀(ℕ, F))
    (hlam : 1 ≤ lam)
    (hf : ContDiffOn ℝ (r : ℕ∞ω) f (Metric.ball 0 s))
    (hC : ContDiffOn ℝ (r : ℕ∞ω) C (Metric.ball 0 s))
    (hformula : ∀ w ∈ Metric.ball (0 : C₀(ℕ, E)) s, ∀ n : ℕ,
      C w n = (lam ^ n) • f ((lam ^ n)⁻¹ • w n))
    (m : ℕ) (hmr : (m : ℕ∞) ≤ r)
    (w : C₀(ℕ, E)) (hw : w ∈ Metric.ball (0 : C₀(ℕ, E)) s)
    (h : Fin m → C₀(ℕ, E)) (n : ℕ) :
    (iteratedFDerivWithin ℝ m C (Metric.ball (0 : C₀(ℕ, E)) s) w h) n =
      lam ^ (((1 : ℤ) - (m : ℤ)) * (n : ℤ)) •
        iteratedFDerivWithin ℝ m f (Metric.ball (0 : E) s)
          ((lam ^ n)⁻¹ • w n) (fun j ↦ h j n) := by
  have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hscaled (z : C₀(ℕ, E)) (hz : z ∈ Metric.ball (0 : C₀(ℕ, E)) s) (i : ℕ) :
      (lam ^ i)⁻¹ • z i ∈ Metric.ball (0 : E) s := by
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    calc
      ‖(lam ^ i)⁻¹ • z i‖ = (lam ^ i)⁻¹ * ‖z i‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (pow_pos hlam0 i).le)]
      _ ≤ 1 * ‖z i‖ := mul_le_mul_of_nonneg_right
        (inv_le_one_of_one_le₀ (one_le_pow₀ hlam)) (norm_nonneg _)
      _ ≤ ‖z‖ := by simpa using BoundedContinuousFunction.norm_coe_le_norm z.toBCF i
      _ < s := hz
  let evE : C₀(ℕ, E) →L[ℝ] E :=
    ({ toFun := fun z ↦ z n
       map_add' := fun _ _ ↦ rfl
       map_smul' := fun _ _ ↦ rfl } : C₀(ℕ, E) →ₗ[ℝ] E).mkContinuous 1
      (fun z ↦ by simpa using BoundedContinuousFunction.norm_coe_le_norm z.toBCF n)
  let evF : C₀(ℕ, F) →L[ℝ] F :=
    ({ toFun := fun z ↦ z n
       map_add' := fun _ _ ↦ rfl
       map_smul' := fun _ _ ↦ rfl } : C₀(ℕ, F) →ₗ[ℝ] F).mkContinuous 1
      (fun z ↦ by simpa using BoundedContinuousFunction.norm_coe_le_norm z.toBCF n)
  let g : C₀(ℕ, E) →L[ℝ] E := (lam ^ n)⁻¹ • evE
  let out : F →L[ℝ] F := (lam ^ n) • ContinuousLinearMap.id ℝ F
  have hm' : (m : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hmr
  have hopen : IsOpen (g ⁻¹' Metric.ball (0 : E) s) :=
    Metric.isOpen_ball.preimage g.continuous
  have hgmem : g w ∈ Metric.ball (0 : E) s := hscaled w hw n
  have hmaps : Set.MapsTo g (Metric.ball (0 : C₀(ℕ, E)) s)
      (Metric.ball (0 : E) s) := fun z hz ↦ hscaled z hz n
  have hcomp : ContDiffOn ℝ (r : ℕ∞ω) (f ∘ g)
      (Metric.ball (0 : C₀(ℕ, E)) s) :=
    (hf.comp_continuousLinearMap g).mono hmaps
  have heq : Set.EqOn (evF ∘ C) (out ∘ (f ∘ g))
      (Metric.ball (0 : C₀(ℕ, E)) s) := fun z hz ↦ hformula z hz n
  have hsets : iteratedFDerivWithin ℝ m (f ∘ g)
      (Metric.ball (0 : C₀(ℕ, E)) s) w =
      iteratedFDerivWithin ℝ m (f ∘ g) (g ⁻¹' Metric.ball (0 : E) s) w := by
    rw [iteratedFDerivWithin_of_isOpen m Metric.isOpen_ball hw,
      iteratedFDerivWithin_of_isOpen m hopen hgmem]
  have heval := evF.iteratedFDerivWithin_comp_left (hC w hw)
    Metric.isOpen_ball.uniqueDiffOn hw hm'
  have hout := out.iteratedFDerivWithin_comp_left (hcomp w hw)
    Metric.isOpen_ball.uniqueDiffOn hw hm'
  have hright := g.iteratedFDerivWithin_comp_right hf Metric.isOpen_ball.uniqueDiffOn
    hopen.uniqueDiffOn hgmem hm'
  have hjet := congrArg (fun A : ContinuousMultilinearMap ℝ
    (fun _ : Fin m ↦ C₀(ℕ, E)) F ↦ A h)
    ((heval.symm.trans (iteratedFDerivWithin_congr heq hw m)).trans hout)
  rw [hsets, hright] at hjet
  change ((iteratedFDerivWithin ℝ m C (Metric.ball 0 s) w) h) n =
    lam ^ n • (iteratedFDerivWithin ℝ m f (Metric.ball 0 s)
      ((lam ^ n)⁻¹ • w n)) (fun j ↦ (lam ^ n)⁻¹ • h j n) at hjet
  rw [hjet, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_smul]
  congr 1
  rw [← zpow_natCast, ← zpow_neg, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hlam0.ne']
  congr 1
  ring

end HolomorphicAnosov.Analysis

