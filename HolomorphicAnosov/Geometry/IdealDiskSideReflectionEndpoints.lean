import HolomorphicAnosov.Geometry.IdealDiskTriangle
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-! This file proves that the literal reflection in a disk side fixes its two ideal endpoints. (Lyubich, §2.4.4) -/

namespace HolomorphicAnosov
open scoped ComplexConjugate

/-- Reflection in a side with distinct ideal endpoints fixes both endpoints. (Lyubich, §2.4.4) -/
theorem idealDiskSideReflection_endpoints {a b : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) :
    idealDiskSideReflection a b a = a ∧ idealDiskSideReflection a b b = b := by
  have hfirst {a b : ℂ} (ha : ‖a‖ = 1) (hab : a ≠ b) :
      idealDiskSideReflection a b a = a := by
    have hunit : a * conj a = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
      norm_num
    have hden : 2 - (a + b) * conj a ≠ 0 := by
      intro he
      apply hab
      linear_combination a * he + (a + b) * hunit
    unfold idealDiskSideReflection
    apply (div_eq_iff hden).mpr
    linear_combination (a - b) * hunit
  have hsecond {a b : ℂ} (hb : ‖b‖ = 1) (hab : a ≠ b) :
      idealDiskSideReflection a b b = b := by
    have hunit : b * conj b = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hb]
      norm_num
    have hden : 2 - (a + b) * conj b ≠ 0 := by
      intro he
      have hconj : conj b * b = 1 := by simpa [mul_comm] using hunit
      have hab' : a * conj b = 1 := by
        calc
          a * conj b = (a + b) * conj b - b * conj b := by ring
          _ = 2 - b * conj b := by
            linear_combination -he
          _ = 1 := by rw [hunit]; norm_num
      apply hab
      calc
        a = a * (conj b * b) := by rw [hconj]; simp
        _ = (a * conj b) * b := by ring
        _ = b := by rw [hab']; simp
    unfold idealDiskSideReflection
    apply (div_eq_iff hden).mpr
    linear_combination (b - a) * hunit
  exact ⟨hfirst ha hab, hsecond hb hab⟩

end HolomorphicAnosov
