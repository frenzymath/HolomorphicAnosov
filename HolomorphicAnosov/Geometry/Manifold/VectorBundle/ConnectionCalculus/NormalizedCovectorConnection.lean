import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

open scoped ContDiff

namespace HolomorphicAnosov.ConnectionCalculus

/-- A holomorphic covector `θ` and transverse field `T` with `θ(T) = 1` admit a holomorphic
connection covector `A` satisfying `A(T) = 0` and `dθ + A ∧ θ = 0`, provided `dθ` vanishes on
pairs of kernel vectors. (Zhang, §2.1, (2)–(4), pp.4–5 and Lemma 2.4, (12)–(13), p.7) -/
theorem normalized_covector_connection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (θ : E → E →L[ℂ] ℂ) (T : E → E) {O : Set E}
    (hO : IsOpen O) (hθ : ContDiffOn ℂ ∞ θ O) (hT : ContDiffOn ℂ ∞ T O)
    (hnormal : ∀ z ∈ O, θ z (T z) = 1)
    (hkernel : ∀ z ∈ O, ∀ v w, θ z v = 0 → θ z w = 0 →
      fderiv ℂ θ z v w - fderiv ℂ θ z w v = 0) :
    ∃ A : E → E →L[ℂ] ℂ, ContDiffOn ℂ ∞ A O ∧
      (∀ z ∈ O, A z (T z) = 0) ∧
      (∀ z ∈ O, ∀ v w, fderiv ℂ θ z v w - fderiv ℂ θ z w v +
        A z v * θ z w - A z w * θ z v = 0) := by
  let D := fderiv ℂ θ
  let A : E → E →L[ℂ] ℂ := fun z ↦ D z (T z) - (D z).flip (T z)
  have hD : ContDiffOn ℂ ∞ D O := hθ.fderiv_of_isOpen hO (by simp)
  refine ⟨A, ?_, ?_, ?_⟩
  · apply contDiffOn_clm_apply.mpr
    intro v
    exact ((hD.clm_apply hT).clm_apply contDiffOn_const).sub
      ((hD.clm_apply contDiffOn_const).clm_apply hT)
  · intro z _
    simp [A]
  · intro z hz v w
    let B : E →L[ℂ] E →L[ℂ] ℂ := D z - (D z).flip
    have halt (a b : E) : B a b = - B b a := by
      simp only [B, sub_apply, ContinuousLinearMap.flip_apply]
      ring
    have hv : θ z (v - θ z v • T z) = 0 := by simp [hnormal z hz]
    have hw : θ z (w - θ z w • T z) = 0 := by simp [hnormal z hz]
    have h := hkernel z hz (v - θ z v • T z) (w - θ z w • T z) hv hw
    change B (v - θ z v • T z) (w - θ z w • T z) = 0 at h
    have hTT : B (T z) (T z) = 0 := by simp [B]
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul] at h
    rw [hTT, halt v (T z)] at h
    have hAv : A z v = B (T z) v := rfl
    have hAw : A z w = B (T z) w := rfl
    change B v w + A z v * θ z w - A z w * θ z v = 0
    rw [hAv, hAw]
    linear_combination h

end HolomorphicAnosov.ConnectionCalculus

