import HolomorphicAnosov.Topology.SingularBarycentricSubdivisionGeometryDefs
import HolomorphicAnosov.Topology.BarycentricHullBridge
import HolomorphicAnosov.Topology.BarycentricIteratedMesh

/-!
# Containment of iterated barycentric faces

Source: Hatcher, *Algebraic Topology*, Proposition 2.21(1), printed pp.119–121.
Every finite-depth permutation-prefix cell, including its nonempty subfaces,
lies in the original Euclidean simplex.
-/

noncomputable section
open Set _root_.Topology
open scoped Classical BigOperators
namespace HolomorphicAnosov.BarycentricGeometry

/-- All finite-depth barycentric cells lie in the original Euclidean simplex.
Source: Hatcher, Algebraic Topology, Proposition 2.21(1), pp.119–121.
A subface lies in its descendant hull by convex-hull monotonicity, and the
iterated mesh theorem places this hull in the original hull. -/
theorem iteratedFaces_hull_subset (n r : ℕ)
    (s : Finset (EuclideanSpace ℝ (Fin (n + 1))))
    (hs : s ∈ iteratedFaces (standardVertices n) r) :
    convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ euclideanSimplex n := by
  have hSimplex (n : ℕ) : euclideanSimplex n = convexHull ℝ (range (standardVertices n)) := by
    let e := (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm
    have hweights :
        range (fun t : Convexity.StdSimplex ℝ (Fin (n + 1)) ↦
          fun i ↦ t.weights i) = {f : Fin (n + 1) → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1} := by
      rw [Convexity.StdSimplex.range_toFun_comp_weights]
      ext x
      simp
    have hsimplex : euclideanSimplex n =
        e '' {f : Fin (n + 1) → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1} := by
      rw [← hweights, ← range_comp]
      rfl
    have hconvex : Convex ℝ
        {f : Fin (n + 1) → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1} := by
      intro f hf g hg a b ha hb hab
      refine ⟨fun i ↦ add_nonneg (mul_nonneg ha (hf.1 i))
        (mul_nonneg hb (hg.1 i)), ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hf.2, hg.2, mul_one, hab]
    have hhull : convexHull ℝ (range (fun i : Fin (n + 1) ↦ Pi.single i (1 : ℝ))) =
        {f : Fin (n + 1) → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1} := by
      classical
      refine Subset.antisymm (convexHull_min ?_ hconvex) ?_
      · rintro _ ⟨i, rfl⟩
        exact ⟨fun j ↦ by simp [Pi.single_apply]; positivity, by simp [Pi.single_apply]⟩
      · rintro w ⟨hw₀, hw₁⟩
        rw [pi_eq_sum_univ w, ← Finset.univ.centerMass_eq_of_sum_1 _ hw₁]
        exact Finset.univ.centerMass_mem_convexHull (fun i _ ↦ hw₀ i)
          (hw₁.symm ▸ zero_lt_one) fun i _ ↦
            ⟨i, by funext j; simp [Pi.single_apply, eq_comm]⟩
    rw [hsimplex, ← hhull]
    change e.toLinearMap '' convexHull ℝ (range (fun i ↦ Pi.single i 1)) = _
    rw [e.toLinearMap.image_convexHull, ← range_comp]
    congr 1
  let : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
  obtain ⟨p, hp, A, hA, rfl⟩ := hs
  have h := (BarycentricMesh.iterated_mesh_contraction n (standardVertices n)).2.1 p
  rw [barycentricMesh_hull_eq_convexHull_range,
    barycentricMesh_hull_eq_convexHull_range, ← hSimplex] at h
  refine (convexHull_mono ?_).trans h
  rw [Finset.coe_image]
  exact Set.image_subset_range _ _

end HolomorphicAnosov.BarycentricGeometry
