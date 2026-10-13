import HolomorphicAnosov.Analysis.Complex.WindingNumber
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Analytic.Order
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.Definitions
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingIncrement

open Set Bundle TopologicalSpace
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section


lemma loopWinding_homotopy (γ₀ γ₁ : ComplexLoop) (b : ℂ)
    (hb₀ : ∀ z, γ₀ z ≠ b) (hb₁ : ∀ z, γ₁ z ≠ b)
    (h : LoopHomotopyAvoids γ₀ γ₁ b) :
    loopWinding γ₀ b hb₀ = loopWinding γ₁ b hb₁ := by
  obtain ⟨H, h0, h1, hne⟩ := h
  let C : C(↑unitInterval × ↑unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun ts ↦ ⟨H (ts.2, Circle.exp (2 * Real.pi * (ts.1 : ℝ))) - b,
      sub_ne_zero.mpr (hne _ _)⟩, by fun_prop⟩
  let c : C(↑unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun s ↦ C (0, s), by fun_prop⟩
  let e := Complex.log (c 0)
  have he : c 0 = (⟨Complex.exp e, Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}) :=
    Subtype.ext (Complex.exp_log (c 0).property).symm
  let l := Complex.isCoveringMap_exp.liftPath c e he
  have hl : ∀ s, C (0, s) =
      (⟨Complex.exp (l s), Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}) :=
    fun s ↦ (congrFun (Complex.isCoveringMap_exp.liftPath_lifts c e he) s).symm
  let L := Complex.isCoveringMap_exp.liftHomotopy C l hl
  have hL : ∀ t s, Complex.exp (L (t, s)) = (C (t, s) : ℂ) :=
    fun t s ↦ congrArg Subtype.val (congrFun
      (Complex.isCoveringMap_exp.liftHomotopy_lifts C l hl) (t, s))
  have hperiod (s : unitInterval) : C (1, s) = C (0, s) := by
    apply Subtype.ext
    dsimp [C]
    congr 3
    apply Subtype.ext
    simp [Circle.coe_exp, Complex.exp_two_pi_mul_I]
  have hdelta := Complex.isCoveringMap_exp.const_of_comp
    (show Continuous (fun s ↦ L (1, s) - L (0, s)) by fun_prop)
    (show ∀ s s',
      (⟨Complex.exp (L (1, s) - L (0, s)), Complex.exp_ne_zero _⟩ :
        {z : ℂ // z ≠ 0}) =
      ⟨Complex.exp (L (1, s') - L (0, s')), Complex.exp_ne_zero _⟩ from by
        intro s s'
        apply Subtype.ext
        simp only [Complex.exp_sub, hL, hperiod]
        simp only [div_self (C (0, _)).property])
    (0 : unitInterval) (1 : unitInterval)
  let L₀ : C(↑unitInterval, ℂ) := ⟨fun t ↦ L (t, 0), by fun_prop⟩
  let L₁ : C(↑unitInterval, ℂ) := ⟨fun t ↦ L (t, 1), by fun_prop⟩
  have hi0 := loopWinding_increment γ₀ b hb₀ L₀ (fun t ↦ by
    simpa [C, L₀, puncturedLoopPath, h0] using hL t 0)
  have hi1 := loopWinding_increment γ₁ b hb₁ L₁ (fun t ↦ by
    simpa [C, L₁, puncturedLoopPath, h1] using hL t 1)
  have hτ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hh : (loopWinding γ₀ b hb₀ : ℂ) * (2 * Real.pi * Complex.I) =
      (loopWinding γ₁ b hb₁ : ℂ) * (2 * Real.pi * Complex.I) := by
    exact hi0.symm.trans (hdelta.trans hi1)
  exact_mod_cast mul_right_cancel₀ hτ hh


end
end HolomorphicAnosov
