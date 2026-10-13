import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.Module.Submodule.Map

/-! A real subspace invariant under the complex structure determines a unique complex submodule with
that realification. (Ghys, Lemma 2.1, p.589) -/

namespace HolomorphicAnosov.StableFoliationsSupport

/-- A real submodule invariant under transported multiplication by `I` is the realification of a
unique complex submodule. (Ghys, Lemma 2.1, p.589) -/
theorem existsUnique_complexSubmodule_of_J_invariant
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
    [IsScalarTower ℝ ℂ V] [AddCommGroup W] [Module ℝ W]
    (e : V ≃ₗ[ℝ] W) (P : Submodule ℝ W)
    (hJ : ∀ w ∈ P, e (Complex.I • e.symm w) ∈ P) :
    ∃! S : Submodule ℂ V, (S.restrictScalars ℝ).map e.toLinearMap = P := by
  let S : Submodule ℂ V := {
    carrier := {v | e v ∈ P}
    zero_mem' := by simp
    add_mem' := by
      intro v w hv hw
      change e (v + w) ∈ P
      rw [map_add]
      exact P.add_mem hv hw
    smul_mem' := by
      intro z v hv
      change e (z • v) ∈ P
      have hi : e (Complex.I • v) ∈ P := by
        simpa only [e.symm_apply_apply] using hJ (e v) hv
      rw [← Complex.re_add_im z, add_smul, mul_smul]
      change e ((algebraMap ℝ ℂ z.re) • v +
        (algebraMap ℝ ℂ z.im) • (Complex.I • v)) ∈ P
      simp only [algebraMap_smul, map_add, map_smul]
      exact P.add_mem (P.smul_mem z.re hv) (P.smul_mem z.im hi) }
  have hS : (S.restrictScalars ℝ).map e.toLinearMap = P := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hw
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      change e (e.symm w) ∈ P
      simpa using hw
  refine ⟨S, hS, ?_⟩
  intro U hU
  apply Submodule.restrictScalars_injective ℝ ℂ V
  exact Submodule.map_injective_of_injective e.injective (hU.trans hS.symm)

end HolomorphicAnosov.StableFoliationsSupport
