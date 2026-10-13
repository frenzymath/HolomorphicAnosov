import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection

namespace HolomorphicAnosov.LatticeDensityPreparation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The projection onto one of two complementary subspaces commutes with a linear map preserving
both subspaces. (Zhang, Lemma 3.1) -/
theorem projection_commutes (P Q : Submodule ℝ V) (h : IsCompl P Q)
    (L : V →ₗ[ℝ] V) (hP : ∀ v ∈ P, L v ∈ P) (hQ : ∀ v ∈ Q, L v ∈ Q) (v : V) :
    P.projection Q h (L v) = L (P.projection Q h v) := by
  conv_lhs => rw [← Submodule.projection_add_projection_eq_self h v]
  rw [map_add, map_add, Submodule.projection_apply_of_mem_left h
    (hP _ (Submodule.projection_apply_mem h v)),
    Submodule.projection_apply_of_mem_right h (hQ _ (Submodule.projection_apply_mem h.symm v)),
    add_zero]

end HolomorphicAnosov.LatticeDensityPreparation
