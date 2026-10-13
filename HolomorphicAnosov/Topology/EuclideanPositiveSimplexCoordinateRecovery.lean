import HolomorphicAnosov.Topology.EuclideanPositiveSimplex
import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Tactic.Linarith

noncomputable section
open Convexity
namespace HolomorphicAnosov

/-- Recover the first barycentric coordinate of the prescribed ordered simplex
from its Euclidean image. This is the elementary coordinate calculation needed
in the embedded-simplex comparison in Hatcher's local-orientation construction,
Algebraic Topology pp.233–234 and ordered edge convention p.269. The particular
formula is the project's coordinate choice; the calculation is agent-written.
Sum the coordinate differences and use that the n+1 weights sum to one.
The formula includes n=0, where the empty coordinate sum is zero. -/
theorem euclideanPositiveSimplex_coordinate_recovery (n : ℕ)
    (t : StdSimplex ℝ (Fin (n + 1))) :
    t.weights 0 = (1 - ∑ j : Fin n, euclideanPositiveSimplex n t j) / (n + 1 : ℝ) := by
  have hsum := t.total_of_fintype
  rw [Fin.sum_univ_succ] at hsum
  have hcoords : (∑ j : Fin n, euclideanPositiveSimplex n t j) =
      (∑ j : Fin n, t.weights j.succ) - (n : ℝ) * t.weights 0 := by
    simp only [euclideanPositiveSimplex, ContinuousMap.coe_mk, WithLp.ofLp_toLp]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  apply (eq_div_iff (by positivity : (n + 1 : ℝ) ≠ 0)).mpr
  linarith

end HolomorphicAnosov
