import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.Definitions
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.IntegralToralMap_measurePreserving
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.MFourier_integralToralMap
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.Transpose_frequency_orbit_injective

import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Eigenspace.Matrix

namespace HolomorphicAnosov.Dynamics
open MeasureTheory
noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

set_option backward.isDefEq.respectTransparency false in
theorem invariant_l2_ae_const {n : ℕ} [NeZero n]
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hroot : ∀ μ : ℂ,
      Module.End.HasEigenvalue (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ →
        ¬ IsOfFinOrder μ)
    (φ : Lp ℂ 2 (maneUnitTorusHaar n))
    (hφ : φ ∘ integralToralMap A =ᵐ[maneUnitTorusHaar n] φ) :
    ∃ c : ℂ, φ =ᵐ[maneUnitTorusHaar n] fun _ ↦ c := by
  classical
  change Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin n))) at φ
  change φ ∘ integralToralMap A =ᵐ[volume] φ at hφ
  change ∃ c : ℂ, φ =ᵐ[volume] fun _ ↦ c
  let b := UnitAddTorus.mFourierBasis (d := Fin n)
  let τ : (Fin n → ℤ) → (Fin n → ℤ) := A.val.transpose.mulVec
  let U := Lp.compMeasurePreservingₗᵢ ℂ (integralToralMap A)
    (integralToralMap_measurePreserving A) (p := 2) (E := ℂ)
  have hUφ : U φ = φ :=
    Lp.ext ((Lp.coeFn_compMeasurePreserving φ
      (integralToralMap_measurePreserving A)).trans hφ)
  have hUb (k : Fin n → ℤ) : U (b k) = b (τ k) := by
    apply Lp.ext
    have hleft := Lp.coeFn_compMeasurePreserving (b k)
      (integralToralMap_measurePreserving A)
    have hsource : (b k : UnitAddTorus (Fin n) → ℂ) =ᵐ[maneUnitTorusHaar n]
        UnitAddTorus.mFourier k := by
      change (b k : UnitAddTorus (Fin n) → ℂ) =ᵐ[volume] UnitAddTorus.mFourier k
      simpa only [b, UnitAddTorus.coe_mFourierBasis] using
        UnitAddTorus.coeFn_mFourierLp 2 k
    have hright : (b (τ k) : UnitAddTorus (Fin n) → ℂ) =ᵐ[maneUnitTorusHaar n]
        UnitAddTorus.mFourier (τ k) := by
      change (b (τ k) : UnitAddTorus (Fin n) → ℂ) =ᵐ[volume]
        UnitAddTorus.mFourier (τ k)
      simpa only [b, UnitAddTorus.coe_mFourierBasis] using
        UnitAddTorus.coeFn_mFourierLp 2 (τ k)
    filter_upwards [hleft,
      (integralToralMap_measurePreserving A).quasiMeasurePreserving.ae_eq_comp hsource,
      hright] with x hx hs ht
    exact hx.trans (hs.trans ((mFourier_integralToralMap A k x).trans ht.symm))
  have hcoeff (k : Fin n → ℤ) : b.repr φ (τ k) = b.repr φ k := by
    rw [b.repr_apply_apply, b.repr_apply_apply]
    calc
      inner ℂ (b (τ k)) φ = inner ℂ (U (b k)) (U φ) := by rw [hUb, hUφ]
      _ = inner ℂ (b k) φ := U.inner_map_map _ _
  have hiter (k : Fin n → ℤ) (r : ℕ) : b.repr φ (τ^[r] k) = b.repr φ k := by
    induction r with
    | zero => rfl
    | succ r ih => rw [Function.iterate_succ_apply', hcoeff, ih]
  have hzero (k : Fin n → ℤ) (hk : k ≠ 0) : b.repr φ k = 0 := by
    have hsum : Summable (fun k : Fin n → ℤ ↦ ‖b.repr φ k‖ ^ (2 : ℝ)) :=
      (lp.memℓp (b.repr φ)).summable (by norm_num)
    have horbit := hsum.comp_injective (transpose_frequency_orbit_injective A hroot k hk)
    have hconst : Summable (fun _ : ℕ ↦ ‖b.repr φ k‖ ^ (2 : ℝ)) := by
      change Summable (fun r : ℕ ↦ ‖b.repr φ (τ^[r] k)‖ ^ (2 : ℝ)) at horbit
      simpa only [hiter] using horbit
    have hn : ‖b.repr φ k‖ ^ (2 : ℝ) = 0 := (summable_const_iff _).mp hconst
    have : ‖b.repr φ k‖ = 0 := by
      have hn' : ‖b.repr φ k‖ ^ (2 : ℕ) = 0 := by simpa using hn
      exact sq_eq_zero_iff.mp hn'
    exact norm_eq_zero.mp this
  have heq : φ = b.repr φ 0 • b 0 := by
    apply b.repr.injective
    ext k
    by_cases hk : k = 0
    · subst k
      simp [HilbertBasis.repr_self, lp.single_apply]
    · simp [HilbertBasis.repr_self, lp.single_apply, hk, hzero k hk]
  let c : ℂ := b.repr φ 0
  refine ⟨c, ?_⟩
  have hφeq : φ = c • b 0 := heq
  rw [hφeq]
  have h0 : (b (0 : Fin n → ℤ) : UnitAddTorus (Fin n) → ℂ) =ᵐ[maneUnitTorusHaar n]
      fun _ ↦ 1 := by
    change (b (0 : Fin n → ℤ) : UnitAddTorus (Fin n) → ℂ) =ᵐ[volume] fun _ ↦ 1
    have hb0 : (b (0 : Fin n → ℤ) : UnitAddTorus (Fin n) → ℂ) =ᵐ[volume]
        UnitAddTorus.mFourier 0 := by
      simpa only [b, UnitAddTorus.coe_mFourierBasis] using
        UnitAddTorus.coeFn_mFourierLp 2 (0 : Fin n → ℤ)
    filter_upwards [hb0] with x hx
    simpa only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply] using hx
  filter_upwards [Lp.coeFn_smul c (b 0), h0] with x hx hz
  simpa only [Pi.smul_apply, hz, smul_eq_mul, mul_one] using hx

-- Mañé II§2 Proposition 2.6: use the backward-semistable union, not false exact invariance.

end
end HolomorphicAnosov.Dynamics
