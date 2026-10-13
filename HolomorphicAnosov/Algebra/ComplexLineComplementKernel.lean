import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Analysis.Complex.Basic

namespace HolomorphicAnosov

/-- A nonzero complex scalar functional annihilating a real complement to a
complex line is injective on that line, transported through any real linear
equivalence.

Source: pinned Mathlib `exists_smul_eq_of_finrank_eq_one`, the decomposition
`Submodule.mem_sup` and `IsCompl.sup_eq_top`. This is the conditional
one-dimensional specialization of those spanning and decomposition identities.

Proof: a nonzero vector in the line's kernel would span the complex line, so
the functional would vanish on the whole line. It already vanishes on the
real complement. Every vector is the sum of vectors in these two real
summands, so the functional would be zero, contradicting the hypothesis.
No complex structure on the complementary real summand is assumed. -/
theorem complexLineComplement_scalar_injective
    {V R : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
    [IsScalarTower ℝ ℂ V] [AddCommGroup R] [Module ℝ R]
    (e : V ≃ₗ[ℝ] R) (S : Submodule ℂ V) (U : Submodule ℝ R)
    (hS : Module.finrank ℂ S = 1)
    (hSU : IsCompl ((S.restrictScalars ℝ).map e.toLinearMap) U)
    (L : V →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    (hU : ∀ v ∈ U, L (e.symm v) = 0) :
    ∀ v ∈ (S.restrictScalars ℝ).map e.toLinearMap,
      L (e.symm v) = 0 → v = 0 := by
  rintro v ⟨z, hz, rfl⟩ hzero
  change L (e.symm (e z)) = 0 at hzero
  simp only [LinearEquiv.symm_apply_apply] at hzero
  by_contra hv
  have hz0 : z ≠ 0 := by
    intro h
    exact hv (by simp [h])
  have hkill : ∀ w ∈ S, L w = 0 := by
    intro w hw
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hS
      (x := (⟨z, hz⟩ : S)) (fun h ↦ hz0 (congrArg Subtype.val h)) (⟨w, hw⟩ : S)
    have hc' : c • z = w := congrArg Subtype.val hc
    rw [← hc', map_smul, hzero, smul_zero]
  apply hL
  ext w
  change L w = 0
  have hw : e w ∈ ((S.restrictScalars ℝ).map e.toLinearMap) ⊔ U := by
    rw [hSU.sup_eq_top]
    trivial
  obtain ⟨s, hs, u, hu, heq⟩ := Submodule.mem_sup.mp hw
  obtain ⟨t, ht, rfl⟩ := hs
  change e t + u = e w at heq
  have heq' := congrArg e.symm heq
  simp only [map_add, LinearEquiv.symm_apply_apply] at heq'
  rw [← heq', map_add, hkill t ht, hU u hu, add_zero]

end HolomorphicAnosov

