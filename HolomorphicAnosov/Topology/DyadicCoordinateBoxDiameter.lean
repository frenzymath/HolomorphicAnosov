import Mathlib.Analysis.InnerProductSpace.PiL2

namespace HolomorphicAnosov

open Set

/--
The Euclidean diameter of a coordinate box is bounded by the side bound times
the square root of the ambient dimension.  This is the metric estimate used in
Hatcher's dyadic complement construction (Algebraic Topology, proof of
Theorem A.7, pp. 525--526).
-/
theorem euclidean_coordinate_box_diameter_le
    {N : ℕ} (s : ℝ) (hs : 0 ≤ s)
    {x y : EuclideanSpace ℝ (Fin N)}
    (hxy : ∀ i, dist (x i) (y i) ≤ s) :
    dist x y ≤ Real.sqrt N * s := by
  rw [EuclideanSpace.dist_eq]
  have hsum : (∑ i, dist (x i) (y i) ^ 2) ≤ ∑ _i : Fin N, s ^ 2 := by
    exact Finset.sum_le_sum (fun i _ ↦ by
      exact (sq_le_sq₀ (dist_nonneg) hs).mpr (hxy i))
  have hsqrt : Real.sqrt (∑ i, dist (x i) (y i) ^ 2) ≤
      Real.sqrt (∑ _i : Fin N, s ^ 2) := Real.sqrt_le_sqrt hsum
  have hconst : (∑ _i : Fin N, s ^ 2) = (N : ℝ) * s ^ 2 := by simp
  rw [hconst] at hsqrt
  simpa [Real.sqrt_mul (by positivity : 0 ≤ (N : ℝ)), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hs] using hsqrt

end HolomorphicAnosov
