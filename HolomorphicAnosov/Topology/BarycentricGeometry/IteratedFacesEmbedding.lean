import HolomorphicAnosov.Topology.BarycentricGeometry.OneStepFacesRestrictionLinearIndependent
import HolomorphicAnosov.Topology.BarycentricGeometry.ChildVerticesLinearIndependent

noncomputable section
open Set
open scoped Classical
namespace HolomorphicAnosov.BarycentricGeometry

/-- Every finite barycentric subdivision of a vertex face is a subcomplex of
that of the whole independent simplex. Source: Schultz, Mathematics 246A §I.2,
Proposition 1 and Corollary 2 p.21, definition p.22, and iteration following
Theorem 4 p.25; Hatcher Proposition 2.21(1), pp.119–121.

Induct on the depth. At depth zero push the chosen vertex indices through the
face embedding. For positive depth, take the first child in the face simplex.
One-step face restriction realizes its full vertex set as a subface of some
child of the whole simplex. Both child tuples are independent. Pull the smaller
child vertices back through the larger child tuple to obtain an injective index
map identifying the actual points. The induction hypothesis embeds the remaining
subdivision path in the larger child; prepend that child's permutation. The
empty path, singleton faces, and a non-monotone face embedding are included. -/
theorem iteratedFaces_embedding_subset {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin (n + 1) → E) (hv : LinearIndependent ℝ v)
    (r m : ℕ) (a : Fin (m + 1) ↪ Fin (n + 1)) :
    iteratedFaces (v ∘ a) r ⊆ iteratedFaces v r := by
  classical
  induction r generalizing v m with
  | zero =>
    rintro s ⟨p, hp, A, hA, rfl⟩
    have hp0 : p = [] := List.length_eq_zero_iff.mp hp
    subst p
    refine ⟨[], rfl, A.image a, hA.image a, ?_⟩
    simp only [BarycentricMesh.iteratedVertices, Finset.image_image]
  | succ r ih =>
    rintro s ⟨p, hp, A, hA, rfl⟩
    cases p with
    | nil => simp at hp
    | cons σ p =>
      have hp' : p.length = r := Nat.succ.inj hp
      let c := BarycentricMesh.childVertices (v ∘ a) σ
      have hc : LinearIndependent ℝ c :=
        childVertices_linearIndependent _ (hv.comp a a.injective) σ
      have hfull : Finset.univ.image c ∈ iteratedFaces (v ∘ a) 1 :=
        ⟨[σ], rfl, Finset.univ, Finset.univ_nonempty, rfl⟩
      have hlift := ((oneStepFaces_restriction_of_linearIndependent v hv m a).symm.subset hfull).1
      obtain ⟨q, hq, B, hB, heq⟩ := hlift
      obtain ⟨τ, rfl⟩ := List.length_eq_one_iff.mp hq
      let d := BarycentricMesh.childVertices v τ
      have hd : LinearIndependent ℝ d := childVertices_linearIndependent v hv τ
      have hcd (i : Fin (m + 1)) : c i ∈ range d := by
        have hi : c i ∈ Finset.univ.image c := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        rw [heq] at hi
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
        exact ⟨j, hj⟩
      have hdc (i : Fin (m + 1)) : d (Function.invFun d (c i)) = c i :=
        Function.invFun_eq (hcd i)
      let b : Fin (m + 1) ↪ Fin (n + 1) := {
        toFun := fun i ↦ Function.invFun d (c i)
        inj' := fun i j hij ↦ hc.injective ((hdc i).symm.trans ((congrArg d hij).trans (hdc j))) }
      have hdb : d ∘ b = c := funext hdc
      have htail : A.image (BarycentricMesh.iteratedVertices c p) ∈ iteratedFaces (d ∘ b) r := by
        rw [hdb]
        exact ⟨p, hp', A, hA, rfl⟩
      obtain ⟨q, hq, B, hB, heq⟩ := ih d hd m b htail
      exact ⟨τ :: q, congrArg Nat.succ hq, B, hB, heq⟩

end HolomorphicAnosov.BarycentricGeometry

