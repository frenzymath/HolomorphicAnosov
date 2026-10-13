import HolomorphicAnosov.Topology.SingularBarycentricSubdivisionGeometryDefs
import HolomorphicAnosov.Topology.BarycentricGeometry.EuclideanSimplexHull
import HolomorphicAnosov.Topology.BarycentricHullBridge

/-! Every maximal permutation-prefix cell is a cone over its proper-prefix flag.
Source: Hatcher, Algebraic Topology, Proposition 2.21(1), pp.119–121;
Schultz, Math246A §I.2, Proposition 3, p.23. -/

noncomputable section
open Set
open scoped Classical
namespace HolomorphicAnosov.BarycentricGeometry

/-- Every permutation cell is the cone over its proper prefix flag.
Source: Hatcher, Proposition 2.21(1), pp.119–121; Schultz §I.2 Proposition 3,
p.23. In dimension zero both families contain the singleton simplex. For a
positive dimension the n proper prefixes form a comparable nonempty family,
have distinct cardinalities, and omit the last vertex. Relabeling the centroid
identifies their barycenters with the first n child vertices; the last child
vertex is the full centroid. Hence their convex hull is the required cone. -/
theorem maximalCells_subset_conedMaximalCells {n : ℕ} :
    maximalCells n ⊆ conedMaximalCells n := by
  intro S hS
  obtain ⟨σ, rfl⟩ := hS
  by_cases hn : n = 0
  · subst n
    have hsimplex : euclideanSimplex 0 = {standardVertices 0 0} := by
      rw [euclideanSimplex_eq_convexHull]
      have hrange : range (standardVertices 0) = {standardVertices 0 0} := by
        ext x
        simp only [mem_range, mem_singleton_iff]
        constructor
        · rintro ⟨i, rfl⟩; rw [Fin.eq_zero i]
        · intro hx; exact ⟨0, hx.symm⟩
      rw [hrange, convexHull_singleton]
    have hcent : ({0} : Finset (Fin 1)).centroid ℝ
        (standardVertices 0 ∘ σ) = standardVertices 0 0 := by
      rw [Finset.centroid_singleton]
      simp [Function.comp, Fin.eq_zero (σ 0)]
    simpa [conedMaximalCells, hsimplex, BarycentricMesh.hull,
      BarycentricMesh.childVertices] using hcent
  · let P (k : Fin n) : OriginalFace n :=
      ⟨(Finset.Iic k.castSucc).image σ,
        Finset.image_nonempty.mpr ⟨k.castSucc, Finset.mem_Iic.mpr le_rfl⟩⟩
    have hPcard (k : Fin n) : (P k).val.card = k.val + 1 := by
      dsimp [P]
      rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Iic]
      rfl
    have hPinj : Function.Injective P := by
      intro k l h
      have hcard := congrArg (fun F : OriginalFace n => F.val.card) h
      rw [hPcard, hPcard] at hcard
      exact Fin.ext (by omega)
    have hPmono (k l : Fin n) (hkl : k ≤ l) : P k ≤ P l := by
      exact Finset.image_subset_image (Finset.Iic_subset_Iic.mpr hkl)
    have hne : ((Finset.univ : Finset (Fin n)).image P).Nonempty := by
      have hpos : 0 < n := Nat.pos_of_ne_zero hn
      exact ⟨P ⟨0, hpos⟩, Finset.mem_image.mpr ⟨⟨0, hpos⟩, Finset.mem_univ _, rfl⟩⟩
    let C : FaceFlag n := PartialOrder.NonemptyFiniteChains.mk
      (Finset.univ.image P) hne (by
        intro a b
        obtain ⟨k, _, hk⟩ := Finset.mem_image.mp a.property
        obtain ⟨l, _, hl⟩ := Finset.mem_image.mp b.property
        rcases le_total k l with h | h
        · left; change a.val ≤ b.val; rw [← hk, ← hl]; exact hPmono k l h
        · right; change b.val ≤ a.val; rw [← hk, ← hl]; exact hPmono l k h)
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
    rw [conedMaximalCells, ite_eq_right hn]
    refine ⟨σ (Fin.last n), C, ?_, ?_, ?_⟩
    · change (Finset.univ.image P).card = n
      rw [Finset.card_image_of_injective _ hPinj]
      simp
    · intro F hF hm
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hF
      obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hm
      have heq' := σ.injective heq
      subst j
      exact (not_le_of_gt (Fin.castSucc_lt_last k)) (Finset.mem_Iic.mp hj)
    · let w := BarycentricMesh.childVertices (standardVertices n) σ
      have hh : BarycentricMesh.hull w = convexHull ℝ (range w) := by
        exact barycentricMesh_hull_eq_convexHull_range w
      rw [hh]
      congr 1
      ext x
      constructor
      · rintro ⟨k, rfl⟩
        refine Fin.lastCases ?_ (fun j => ?_) k
        · exact Or.inl hlast
        · right
          apply Finset.mem_image.mpr
          refine ⟨P j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
          exact (hcent j.castSucc).symm
      · intro hx
        rcases hx with rfl | hx
        · exact ⟨Fin.last n, hlast⟩
        · obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hF
          exact ⟨k.castSucc, hcent k.castSucc⟩

end HolomorphicAnosov.BarycentricGeometry

