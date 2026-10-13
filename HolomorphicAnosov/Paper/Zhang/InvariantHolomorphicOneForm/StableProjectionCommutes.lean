import Mathlib.LinearAlgebra.Projection
import Mathlib.Basic.Real.Basic

open Set



noncomputable section
namespace HolomorphicAnosov.Paper.Zhang


universe u

/-- Projection onto one of two complementary invariant subspaces commutes with the linear dynamics.
(Zhang, Lemma 4.2, p.14) -/
theorem stable_projection_commutes
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S U : Submodule ℝ V) (hSU : IsCompl S U) (A : V →ₗ[ℝ] V)
    (hAS : ∀ v ∈ S, A v ∈ S) (hAU : ∀ v ∈ U, A v ∈ U) (v : V) :
    S.projectionOnto U hSU (A v) =
      ⟨A (S.projectionOnto U hSU v), hAS _ (S.projectionOnto U hSU v).property⟩ := by
  have hu := hAU _ (S.sub_projection_mem hSU v)
  have hz := (S.projectionOnto_apply_eq_zero_iff hSU).mpr hu
  rw [map_sub, map_sub] at hz
  have hs := S.projectionOnto_apply_of_mem_left hSU
    (hAS _ (S.projectionOnto U hSU v).property)
  change S.projectionOnto U hSU (A v) -
    S.projectionOnto U hSU (A (S.projectionOnto U hSU v)) = 0 at hz
  rw [hs] at hz
  exact sub_eq_zero.mp hz


end HolomorphicAnosov.Paper.Zhang
