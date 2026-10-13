import HolomorphicAnosov.Topology.EuclideanPositiveSimplex
import Mathlib.LinearAlgebra.Matrix.SchurComplement

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Convexity
namespace HolomorphicAnosov

/-- The ordered edge matrix of the specified Euclidean simplex has determinant
n+1, hence uses the positive ordered Euclidean orientation in every dimension.
Source: Hatcher, Algebraic Topology p.269, ordered edge-basis convention;
the calculation uses Mathlib's matrix determinant lemma for a rank-one
perturbation of the identity. The prescribed vertices give I+11ᵀ; the
matrix determinant lemma gives 1+sum(1)=n+1, including the empty matrix n=0. -/
theorem euclideanPositiveSimplex_edge_determinant (n : ℕ) :
    Matrix.det (fun i j : Fin n ↦
      euclideanPositiveSimplex n (StdSimplex.single j.succ) i -
        euclideanPositiveSimplex n (StdSimplex.single 0) i) = (n + 1 : ℝ) := by
  have h := Matrix.det_one_add_replicateCol_mul_replicateRow
    (ι := Unit) (fun _ : Fin n ↦ (1 : ℝ)) (fun _ : Fin n ↦ (1 : ℝ))
  have heq : (fun i j : Fin n ↦
      euclideanPositiveSimplex n (StdSimplex.single j.succ) i -
        euclideanPositiveSimplex n (StdSimplex.single 0) i) =
      1 + Matrix.replicateCol Unit (fun _ : Fin n ↦ (1 : ℝ)) *
        Matrix.replicateRow Unit (fun _ : Fin n ↦ (1 : ℝ)) := by
    funext i j
    change _ = (if i = j then (1 : ℝ) else 0) + ∑ _k : Unit, (1 : ℝ) * 1
    simp [euclideanPositiveSimplex, Finsupp.single_apply, eq_comm]
  rw [heq, h]
  simp [dotProduct, add_comm]

end HolomorphicAnosov
