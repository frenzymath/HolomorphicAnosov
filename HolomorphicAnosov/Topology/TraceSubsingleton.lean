import Mathlib.LinearAlgebra.Trace

/-!
# Trace vanishes on a subsingleton finite-dimensional rational module

This general linear-algebra fact is extracted from the compact ENR Lefschetz
local-index proof. It applies to any finite-dimensional module over ℚ whose
underlying additive group is subsingleton.
-/

noncomputable section

/-- A linear endomorphism of a subsingleton finite-dimensional ℚ-module has zero trace.

The endomorphism is pointwise zero by subsingleton elimination, and Mathlib's trace
is additive, hence maps the zero endomorphism to zero.
-/
theorem linearMap_trace_eq_zero_of_subsingleton
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (hV : Subsingleton V) (T : V →ₗ[ℚ] V) :
    LinearMap.trace ℚ V T = 0 := by
  let := hV
  have hT : T = 0 := by
    ext v
    exact Subsingleton.elim _ _
  rw [hT]
  exact map_zero (LinearMap.trace ℚ V)
