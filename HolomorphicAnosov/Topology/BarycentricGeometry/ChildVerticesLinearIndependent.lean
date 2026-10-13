import HolomorphicAnosov.Topology.BarycentricIteratedMesh
import HolomorphicAnosov.Topology.Barycentric.StandardBarycenterCoordinate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import HolomorphicAnosov.Topology.Barycentric.prefix_centroid_eq_smul_sum

/-!
# Independence of prefix-centroid children

Source: Schultz, Mathematics 246A §I.2, Proposition 3 and its triangular independence proof,
printed p.23. The linear-independence strengthening and matrix encoding below are
an agent-written expansion used for the finite-depth affine-independence proof.
DAG node: `topo.child_vertices_linear_independent_g4`.
-/

noncomputable section
open Set
open scoped BigOperators

namespace HolomorphicAnosov.BarycentricGeometry

/-- Prefix-centroid subdivision preserves linear independence of a finite vertex tuple.
Source context: Schultz, Mathematics 246A §I.2, Proposition 3, printed p.23. This
linear-independence strengthening is an agent-written expansion of its triangular proof.
The coordinate prefix barycenters form the rows of a lower triangular matrix. Its
diagonal entries are reciprocals of positive prefix cardinalities, hence nonzero;
the determinant criterion gives linear independence of its rows. The linear map sending each
coordinate unit vector to the corresponding permuted vertex is injective because the
original vertices are linearly independent. It sends these coordinate barycenters to
the prefix centroids, so their images remain linearly independent. This includes the
single-vertex case and requires no spanning or finite-dimensionality hypothesis on E. -/
theorem childVertices_linearIndependent {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : Fin (n + 1) → E)
    (hv : LinearIndependent ℝ v) (σ : Equiv.Perm (Fin (n + 1))) :
    LinearIndependent ℝ (BarycentricMesh.childVertices v σ) := by
  classical
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun k ↦
    ((Finset.Iic k).card : ℝ)⁻¹ •
      ∑ i ∈ Finset.Iic k, (Pi.single i 1 : Fin (n + 1) → ℝ)
  have htri : B.IsLowerTriangular := by
    intro i j hij
    simp only [B, standard_barycenter_coordinate, Finset.mem_Iic]
    exact ite_eq_right (not_le_of_gt hij)
  have hdet : B.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular B htri]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    simp [B, Fin.card_Iic]
    positivity
  have hstd := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  let L : (Fin (n + 1) → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ (v ∘ σ)
  have hL : Function.Injective L :=
    (hv.comp σ σ.injective).fintypeLinearCombination_injective
  have hmap := hstd.map' L (LinearMap.ker_eq_bot.mpr hL)
  convert hmap using 1
  funext k
  change BarycentricMesh.childVertices v σ k =
    L (((Finset.Iic k).card : ℝ)⁻¹ •
      ∑ i ∈ Finset.Iic k, (Pi.single i 1 : Fin (n + 1) → ℝ))
  rw [map_smul, map_sum]
  simp only [L, Fintype.linearCombination_apply_single, one_smul]
  rw [BarycentricMesh.childVertices, prefix_centroid_eq_smul_sum, Fin.card_Iic]

end HolomorphicAnosov.BarycentricGeometry

