import HolomorphicAnosov.Topology.SingularBarycentricSubdivisionGeometryDefs
import HolomorphicAnosov.Topology.BarycentricIteratedMeshDefs
import HolomorphicAnosov.Topology.BarycentricGeometry.MaximalCellsSubsetConed
import HolomorphicAnosov.Topology.BarycentricGeometry.MaximalFaceFlagPermutation
import HolomorphicAnosov.Topology.BarycentricGeometry.EuclideanSimplexHull
import HolomorphicAnosov.Topology.BarycentricHullBridge

noncomputable section
open Set _root_.Topology
open scoped Classical BigOperators
namespace HolomorphicAnosov.BarycentricGeometry

/-- Maximal permutation-prefix cells are precisely the recursively coned cells.
Source: Hatcher, Algebraic Topology, Proposition 2.21(1), pp.119–120;
Schultz, Math 246A §I.2 Proposition 3 proof, printed p.23.
Proof: when n=0 both sides consist of the original singleton. For n>0 remove
the last entry of a permutation; its n proper prefixes form a chain of n
nonempty faces avoiding that entry. Their barycenters, together with the full
barycenter, are its child vertices. Conversely order an n-member chain avoiding
i by cardinality. Strict inclusion strictly increases cardinality, and all
cardinalities lie between 1 and n, so they are exactly 1,...,n. Each successive
set difference is a singleton. Enumerate these singletons and append i. The
resulting permutation has exactly those proper prefixes. Centroid invariance
under index relabeling identifies the finite vertex sets and their hulls. -/
theorem maximalCells_eq_conedMaximalCells (n : ℕ) :
    maximalCells n = conedMaximalCells n := by
  apply Set.Subset.antisymm maximalCells_subset_conedMaximalCells
  intro S hS
  by_cases hn : n = 0
  · subst n
    have hS' : S = euclideanSimplex 0 := by simpa [conedMaximalCells] using hS
    rw [hS']
    refine ⟨Equiv.refl _, ?_⟩
    have hrange : range (standardVertices 0) = {standardVertices 0 0} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩; simp [Fin.eq_zero i]
      · intro hx; exact ⟨0, (Set.mem_singleton_iff.mp hx).symm⟩
    have hsimplex : euclideanSimplex 0 = {standardVertices 0 0} := by
      rw [euclideanSimplex_eq_convexHull, hrange, convexHull_singleton]
    have hcm : ({0} : Finset (Fin 1)).centerMass (Finset.centroidWeights ℝ {0})
        (standardVertices 0) = standardVertices 0 0 := by
      apply Finset.centerMass_singleton
      simp
    simp [hsimplex, BarycentricMesh.hull, BarycentricMesh.childVertices, hcm]
  · rw [conedMaximalCells, ite_eq_right hn] at hS
    obtain ⟨i, C, hc, ha, rfl⟩ := hS
    obtain ⟨σ, hσ⟩ := maximal_face_flag_permutation C i hc ha
    refine ⟨σ, ?_⟩
    rw [barycentricMesh_hull_eq_convexHull_range]
    have hcent (k : Fin (n + 1)) :
        BarycentricMesh.childVertices (standardVertices n) σ k =
          ((Finset.Iic k).image σ).centroid ℝ (standardVertices n) := by
      have hf : Finset.univ.filter (fun j : Fin (n + 1) => j ≤ k) = Finset.Iic k := by
        ext j; simp
      simpa [BarycentricMesh.childVertices, hf, Finset.map_eq_image] using
        (Finset.centroid_map ℝ (Finset.Iic k) σ.toEmbedding (standardVertices n)).symm
    have hlast : BarycentricMesh.childVertices (standardVertices n) σ (Fin.last n) =
        Finset.univ.centroid ℝ (standardVertices n) := by
      rw [hcent]
      congr 1
      ext j
      simp only [Finset.mem_image, Finset.mem_Iic, Fin.le_last, true_and,
        Finset.mem_univ, iff_true]
      exact σ.surjective j
    congr 1
    ext x
    constructor
    · intro hx
      rcases hx with rfl | hx
      · exact ⟨Fin.last n, hlast⟩
      · obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hx
        have hm : F.val ∈ C.finset.image Subtype.val := Finset.mem_image.mpr ⟨F, hF, rfl⟩
        rw [hσ] at hm
        obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hm
        refine ⟨k.castSucc, ?_⟩
        rw [hcent, hk]
        rfl
    · rintro ⟨k, rfl⟩
      refine Fin.lastCases ?_ (fun j => ?_) k
      · exact Or.inl hlast
      · right
        have hm : (Finset.Iic j.castSucc).image σ ∈ C.finset.image Subtype.val := by
          rw [hσ]
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
        obtain ⟨F, hF, hval⟩ := Finset.mem_image.mp hm
        apply Finset.mem_image.mpr
        refine ⟨F, hF, ?_⟩
        rw [hcent]
        change F.val.centroid ℝ (standardVertices n) = _
        rw [hval]


end HolomorphicAnosov.BarycentricGeometry

