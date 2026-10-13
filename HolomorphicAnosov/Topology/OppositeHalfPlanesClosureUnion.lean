import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Closures of opposite half-planes

This file proves that the closures of two complementary local half-planes cover a neighborhood. (Cairns, 2(B))
-/

namespace HolomorphicAnosov

open Set

/-- If two sets agree on opposite strict half-planes in an open neighborhood, their closures cover that neighborhood. (Cairns, 2(B)) -/
theorem opposite_half_planes_closure_union
    (U C₁ C₂ : Set ℂ) (hU : IsOpen U) (x ν : ℂ) (hν : ν ≠ 0)
    (h₁ : U ∩ C₁ = {z : ℂ | z ∈ U ∧ 0 < ((z - x) / ν).re})
    (h₂ : U ∩ C₂ = {z : ℂ | z ∈ U ∧ ((z - x) / ν).re < 0}) :
    U ⊆ closure C₁ ∪ closure C₂ := by
  let e : ℂ ≃ₜ ℂ :=
    (Homeomorph.addRight (-x)).trans (Homeomorph.mulRight₀ ν⁻¹ (inv_ne_zero hν))
  have he (z : ℂ) : e z = (z - x) / ν := by simp [e, sub_eq_add_neg, div_eq_mul_inv]
  have hpos : closure {z : ℂ | 0 < ((z - x) / ν).re} =
      {z : ℂ | 0 ≤ ((z - x) / ν).re} := by
    simpa only [Complex.closure_setOfPred_lt_re, preimage_ofPred_eq, he] using
      (e.preimage_closure {z : ℂ | 0 < z.re}).symm
  have hneg : closure {z : ℂ | ((z - x) / ν).re < 0} =
      {z : ℂ | ((z - x) / ν).re ≤ 0} := by
    simpa only [Complex.closure_setOfPred_re_lt, preimage_ofPred_eq, he] using
      (e.preimage_closure {z : ℂ | z.re < 0}).symm
  intro z hz
  rcases le_total 0 (((z - x) / ν).re) with h | h
  · left
    have hz' : z ∈ closure {w : ℂ | 0 < ((w - x) / ν).re} := by
      rw [hpos]
      exact h
    have hlocal := hU.inter_closure ⟨hz, hz'⟩
    change z ∈ closure {w : ℂ | w ∈ U ∧ 0 < ((w - x) / ν).re} at hlocal
    rw [← h₁] at hlocal
    exact closure_mono inter_subset_right hlocal
  · right
    have hz' : z ∈ closure {w : ℂ | ((w - x) / ν).re < 0} := by
      rw [hneg]
      exact h
    have hlocal := hU.inter_closure ⟨hz, hz'⟩
    change z ∈ closure {w : ℂ | w ∈ U ∧ ((w - x) / ν).re < 0} at hlocal
    rw [← h₂] at hlocal
    exact closure_mono inter_subset_right hlocal

end HolomorphicAnosov
