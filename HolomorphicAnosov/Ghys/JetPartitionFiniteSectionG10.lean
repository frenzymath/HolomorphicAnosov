import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-! Reconstruction from guarded finite affine coefficient sums. Source: Demailly IV.5.11(b), equation (5.12), p.208. -/

noncomputable section
namespace HolomorphicAnosov.Ghys
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Finite subordinate sum-one weights determine a unique original fibre point whose coefficient in every active affine chart is the guarded weighted sum of the local sections. -/
theorem exists_unique_guarded_finite_affine_section
    {X J : Type*} {n : ℕ} (p : J → X) (U : Fin n → Set X)
    (hcover : ∀ x, ∃ i, x ∈ U i)
    (rho : Fin n → X → ℝ) (hsum : ∀ x, ∑ i, rho i x = 1)
    (hzero : ∀ i x, x ∉ U i → rho i x = 0)
    (e : ∀ i x, x ∈ U i → {q : J // p q = x} ≃ ℂ)
    (localSection : ∀ i x, x ∈ U i → {q : J // p q = x})
    (hoverlap : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j),
      ∃ A B : ℂ, ∀ q, e j x hj q = A * e i x hi q + B) :
    ∃! s : ∀ x, {q : J // p q = x},
      ∀ i x (hi : x ∈ U i), e i x hi (s x) =
        ∑ k : Fin n, if hk : x ∈ U k then
          (rho k x : ℂ) * e i x hi (localSection k x hk) else 0 := by
  classical
  choose i hi using hcover
  let b (j : Fin n) (x : X) (hj : x ∈ U j) : ℂ :=
    ∑ k : Fin n, if hk : x ∈ U k then
      (rho k x : ℂ) * e j x hj (localSection k x hk) else 0
  let s (x : X) : {q : J // p q = x} := (e (i x) x (hi x)).symm (b (i x) x (hi x))
  have hformula : ∀ j x (hj : x ∈ U j), e j x hj (s x) = b j x hj := by
    intro j x hj
    obtain ⟨A, B, hab⟩ := hoverlap (i x) j x (hi x) hj
    have hb : b j x hj = A * b (i x) x (hi x) + B := by
      let values (k : Fin n) : ℂ :=
        if hk : x ∈ U k then e (i x) x (hi x) (localSection k x hk) else 0
      let F : ℂ →ᵃ[ℂ] ℂ := (LinearMap.mul ℂ ℂ A).toAffineMap + AffineMap.const ℂ ℂ B
      have hw : ∑ k : Fin n, (rho k x : ℂ) = 1 := by exact_mod_cast hsum x
      have hmap := Finset.map_affineCombination (s := Finset.univ)
        values (fun k ↦ (rho k x : ℂ)) hw F
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw,
        Finset.affineCombination_eq_linear_combination _ _ _ hw] at hmap
      have hleft : (∑ k, (rho k x : ℂ) • values k) = b (i x) x (hi x) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : x ∈ U k <;> simp [values, hk, hzero, smul_eq_mul]
      have hright : (∑ k, (rho k x : ℂ) • (F ∘ values) k) = b j x hj := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : x ∈ U k
        · simp [values, F, hk, hab, smul_eq_mul]
        · simp [values, hk, hzero k x hk]
      rw [hleft, hright] at hmap
      exact hmap.symm
    rw [hab, hb]
    simp [s]
  refine ⟨s, hformula, ?_⟩
  intro t ht
  funext x
  apply (e (i x) x (hi x)).injective
  exact (ht (i x) x (hi x)).trans (hformula (i x) x (hi x)).symm

end HolomorphicAnosov.Ghys

