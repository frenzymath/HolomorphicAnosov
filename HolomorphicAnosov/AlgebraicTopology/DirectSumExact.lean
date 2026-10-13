import HolomorphicAnosov.AlgebraicTopology.SingularRelativeCohomologyPairTheorems
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Exactness of direct sums of componentwise exact linear maps

A finite-support direct sum preserves exactness of a family of linear maps.
This is the direct-sum exactness step used in Hatcher's finite-dimensional
Kunneth induction, p.218.
-/

noncomputable section

open scoped DirectSum

universe u

namespace HolomorphicAnosov.AlgebraicTopology

variable (R : Type u) [CommRing R]

/-- Componentwise exact linear maps induce an exact pair on finite-support
DirectSum modules. -/
theorem directSum_lmap_exact {ι : Type u} (A B C : ι → Type u)
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)] [∀ i, AddCommGroup (C i)]
    [∀ i, Module R (A i)] [∀ i, Module R (B i)] [∀ i, Module R (C i)]
    (f : ∀ i, A i →ₗ[R] B i) (g : ∀ i, B i →ₗ[R] C i)
    (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (DirectSum.lmap f) (DirectSum.lmap g) := by
  classical
  intro x
  constructor
  · intro hx
    have hp : ∀ i : (x.support : Set ι), ∃ a : A i.val, f i.val a = x i.val := by
      intro i
      apply (h i.val (x i.val)).mp
      exact congrArg (fun y : ⨁ i, C i ↦ y i.val) hx
    choose a ha using hp
    refine ⟨DFinsupp.mk x.support a, ?_⟩
    ext i
    by_cases hi : i ∈ x.support
    · simpa only [DirectSum.lmap_apply, DFinsupp.mk_of_mem hi] using ha ⟨i, hi⟩
    · have hz : x i = 0 := by simpa only [DFinsupp.mem_support_toFun, not_not] using hi
      simp only [DirectSum.lmap_apply, DFinsupp.mk_apply, hi, ↓reduceDIte, map_zero, hz]
  · rintro ⟨a, rfl⟩
    ext i
    exact (h i (f i (a i))).mpr ⟨a i, rfl⟩


end HolomorphicAnosov.AlgebraicTopology
