import HolomorphicAnosov.Topology.BarycentricCoverage
import HolomorphicAnosov.Topology.BarycentricIteratedMesh
import HolomorphicAnosov.Topology.SingularBarycentricSubdivisionGeometryDefs

/-!
# Coverage by all iterated barycentric faces

Source context: Hatcher, *Algebraic Topology*, Proposition 2.21(1), pp.119–121.
The finite-set face encoding is expanded by an elementary induction below.
-/

noncomputable section

open Set
open scoped Classical

namespace HolomorphicAnosov.BarycentricGeometry

/-- The convex hulls of all nonempty faces at any fixed subdivision depth cover exactly the
original vertex hull. This holds for degenerate tuples as well as affine-independent ones.

Source: Hatcher, *Algebraic Topology*, proof of Proposition 2.21(1), pp.119–121. This is the
agent-written expansion of the realization clause of `iteratedFaces_simplicialComplex` for the
literal finite-set face encoding. The source-backed one-step coverage theorem is the only
geometric input. At depth zero the full index set gives the original hull, and every subface
lies in it by convex-hull monotonicity. At positive depth split a nonempty permutation list
into its first child and its tail. Induction identifies the union of tail-face hulls with that
child hull; one-step coverage identifies the union of child hulls with the parent hull. In
the reverse direction choose a covering child, apply induction, and prepend its permutation
to the descendant list. No affine independence or simplicial intersection hypothesis is used.
-/
theorem iteratedFaces_convexHull_union {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : Fin (m + 1) → E) (r : ℕ) :
    (⋃ s ∈ iteratedFaces v r, convexHull ℝ (s : Set E)) = convexHull ℝ (range v) := by
  induction r generalizing v with
  | zero =>
      apply Set.Subset.antisymm
      · intro x hx
        rcases Set.mem_iUnion.mp hx with ⟨s, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨hs, hx⟩
        rcases hs with ⟨p, hp, A, _hA, rfl⟩
        have hp0 : p = [] := List.length_eq_zero_iff.mp hp
        subst p
        exact convexHull_mono (by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨i, _hi, rfl⟩
          exact ⟨i, rfl⟩) hx
      · intro x hx
        refine Set.mem_iUnion.mpr ⟨Finset.univ.image v, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
        · exact ⟨[], rfl, Finset.univ, Finset.univ_nonempty, rfl⟩
        · simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using hx
  | succ r ih =>
      have hcover : convexHull ℝ (range v) =
          ⋃ σ : Equiv.Perm (Fin (m + 1)),
            convexHull ℝ (range (BarycentricMesh.childVertices v σ)) :=
        (barycentric_subdivision_coverage (m + 1) v).1
      apply Set.Subset.antisymm
      · intro x hx
        rcases Set.mem_iUnion.mp hx with ⟨s, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨hs, hx⟩
        rcases hs with ⟨p, hp, A, hA, rfl⟩
        cases p with
        | nil => simp at hp
        | cons σ p =>
            have hp' : p.length = r := Nat.succ.inj hp
            rw [hcover]
            apply Set.mem_iUnion.mpr
            refine ⟨σ, ?_⟩
            rw [← ih (BarycentricMesh.childVertices v σ)]
            refine Set.mem_iUnion.mpr ⟨A.image (BarycentricMesh.iteratedVertices
              (BarycentricMesh.childVertices v σ) p), Set.mem_iUnion.mpr ⟨?_, hx⟩⟩
            exact ⟨p, hp', A, hA, rfl⟩
      · intro x hx
        rw [hcover] at hx
        rcases Set.mem_iUnion.mp hx with ⟨σ, hx⟩
        rw [← ih (BarycentricMesh.childVertices v σ)] at hx
        rcases Set.mem_iUnion.mp hx with ⟨s, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨hs, hx⟩
        rcases hs with ⟨p, hp, A, hA, rfl⟩
        refine Set.mem_iUnion.mpr ⟨A.image (BarycentricMesh.iteratedVertices
          (BarycentricMesh.childVertices v σ) p), Set.mem_iUnion.mpr ⟨?_, hx⟩⟩
        exact ⟨σ :: p, congrArg Nat.succ hp, A, hA, rfl⟩

end HolomorphicAnosov.BarycentricGeometry

