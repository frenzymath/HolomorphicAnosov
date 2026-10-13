import HolomorphicAnosov.Topology.SingularBarycentricSubdivisionGeometryDefs
import HolomorphicAnosov.Topology.BarycentricGeometry.FiniteChainPermutationPrefix

noncomputable section
open Set _root_.Topology
open scoped Classical BigOperators
namespace HolomorphicAnosov.BarycentricGeometry

/-- The finite centroid sets of nonempty face flags are precisely the one-step
permutation-prefix descendant faces of any real vertex tuple. This is the same
finite-chain encoding as `flagFaces_eq_iteratedFaces_one`, before specializing
vertices to coordinate vectors. Source: Schultz, Math 246A §I.2, definition p.22
and Proposition 3 proof p.23. Extend the chain of nonempty index sets to a full
permutation flag, select its original members, and use centroid relabeling.
Conversely the selected prefixes of a permutation form a nonempty flag. Repeated
vertices are permitted: this statement records finite images only. -/
theorem flagCentroids_eq_iteratedFaces_one {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : Fin (n + 1) → E) :
    {s | ∃ C : FaceFlag n, s = C.finset.image (fun F ↦ F.val.centroid ℝ v)} =
      iteratedFaces v 1 := by
  classical
  let P : Equiv.Perm (Fin (n + 1)) → Fin (n + 1) → OriginalFace n := fun σ k ↦
    ⟨(Finset.univ.filter (fun j ↦ j ≤ k)).image σ,
      ⟨σ k, Finset.mem_image.mpr
        ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩, rfl⟩⟩⟩
  have hcent : ∀ σ k, (P σ k).val.centroid ℝ v =
      BarycentricMesh.childVertices v σ k := by
    intro σ k
    dsimp [P, BarycentricMesh.childVertices]
    simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using
      (Finset.centroid_map ℝ (Finset.univ.filter (fun j ↦ j ≤ k)) σ.toEmbedding
        v)
  have hmono : ∀ σ, Monotone (P σ) := by
    intro σ k l hkl i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨j,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.trans hkl⟩, rfl⟩
  ext s
  constructor
  · rintro ⟨C, rfl⟩
    let D : Finset (Finset (Fin (n + 1))) := C.finset.image Subtype.val
    have hne : ∀ F ∈ D, F.Nonempty := by
      intro F hF
      obtain ⟨G, _, rfl⟩ := Finset.mem_image.mp hF
      exact G.property
    have hchain : ∀ F ∈ D, ∀ G ∈ D, F ⊆ G ∨ G ⊆ F := by
      intro F hF G hG
      obtain ⟨F', hF', rfl⟩ := Finset.mem_image.mp hF
      obtain ⟨G', hG', rfl⟩ := Finset.mem_image.mp hG
      exact C.comparable ⟨F', hF'⟩ ⟨G', hG'⟩
    obtain ⟨σ, hσ⟩ := finite_chain_exists_permutation_prefix (n + 1) D hne hchain
    have hprefix : ∀ F ∈ C.finset, ∃ k, F = P σ k := by
      intro F hF
      obtain ⟨k, hk⟩ := hσ F.val (Finset.mem_image.mpr ⟨F, hF, rfl⟩)
      exact ⟨k, Subtype.ext hk⟩
    let A := Finset.univ.filter (fun k ↦ P σ k ∈ C.finset)
    have hA : A.Nonempty := by
      obtain ⟨F, hF⟩ := C.nonempty
      obtain ⟨k, rfl⟩ := hprefix F hF
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF⟩⟩
    refine ⟨[σ], rfl, A, hA, ?_⟩
    simp only [BarycentricMesh.iteratedVertices]
    apply Finset.ext
    intro x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨F, hF, hFx⟩
      obtain ⟨k, hFk⟩ := hprefix F hF
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFk ▸ hF⟩, ?_⟩
      exact (hcent σ k).symm.trans ((congrArg (fun F : OriginalFace n ↦ F.val.centroid ℝ v) hFk).symm.trans hFx)
    · rintro ⟨k, hk, hkx⟩
      exact ⟨P σ k, (Finset.mem_filter.mp hk).2, (hcent σ k).trans hkx⟩
  · rintro ⟨p, hp, A, hA, rfl⟩
    obtain ⟨σ, rfl⟩ := List.length_eq_one_iff.mp hp
    let C : FaceFlag n := {
      finset := A.image (P σ)
      nonempty := hA.image _
      comparable := by
        rintro ⟨F, hF⟩ ⟨G, hG⟩
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hF
        obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hG
        rcases le_total k l with h | h
        · exact Or.inl (hmono σ h)
        · exact Or.inr (hmono σ h)
    }
    refine ⟨C, ?_⟩
    simp only [BarycentricMesh.iteratedVertices]
    dsimp [C]
    rw [Finset.image_image]
    ext x
    simp only [Finset.mem_image, Function.comp_apply]
    constructor
    · rintro ⟨k, hk, hkx⟩
      exact ⟨k, hk, (hcent σ k).trans hkx⟩
    · rintro ⟨k, hk, hkx⟩
      exact ⟨k, hk, (hcent σ k).symm.trans hkx⟩

/-- One-step cells, including their nonempty subfaces, are exactly face flags.
Source: Schultz, Math 246A §I.2, barycentric subdivision definition printed p.22
and Proposition 3 proof printed p.23; Hatcher pp.119–120.
Proof: a length-one path is a single permutation. Its prefix index sets form a
strict chain, and a nonempty subset of child vertices selects a nonempty
subchain. Centroid relabeling identifies its vertices with the flag vertices.
Conversely apply the finite-chain permutation-prefix theorem, whose sorting
argument expands Schultz's extension to a full flag. Select precisely those
prefix indices whose original faces belong to the given chain. The centroid
relabeling identity makes their child vertices exactly the original flag's
vertices. No affine independence or injectivity of barycenters is needed. -/
theorem flagFaces_eq_iteratedFaces_one (n : ℕ) :
    flagFaces n = iteratedFaces (standardVertices n) 1 := by
  classical
  rw [← flagCentroids_eq_iteratedFaces_one]
  ext s
  constructor
  · rintro ⟨C, rfl⟩
    refine ⟨C, ?_⟩
    ext x
    simp [flagVertices, faceBarycenter]
  · rintro ⟨C, rfl⟩
    refine ⟨C, ?_⟩
    ext x
    simp [flagVertices, faceBarycenter]

end HolomorphicAnosov.BarycentricGeometry
