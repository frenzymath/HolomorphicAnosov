import HolomorphicAnosov.Topology.BarycentricGeometry.OneStepFacesIntersection
import HolomorphicAnosov.Topology.BarycentricGeometry.OneStepFacesLinearIndependent
import HolomorphicAnosov.Topology.BarycentricGeometry.OneStepFacesRestrictionLinearIndependent
import HolomorphicAnosov.Topology.BarycentricGeometry.IteratedFacesCoverage
import HolomorphicAnosov.Topology.BarycentricGeometry.IteratedFacesNonemptyDownClosed
import HolomorphicAnosov.Topology.SimplicialCommonSubcomplex
import HolomorphicAnosov.Topology.BarycentricGeometry.IteratedFacesAffineIndependent

noncomputable section
open Set _root_.Topology
open scoped Classical BigOperators
namespace HolomorphicAnosov.BarycentricGeometry

/-- Expanding the empty permutation path identifies depth-zero faces with nonempty
subsets of the indexed vertex image. This is the finite-set encoding of the
unsubdivided simplex in Hatcher pp.119–120; no independence is needed. -/
theorem iteratedFaces_zero_iff {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : Fin (m + 1) → E) (s : Finset E) :
    s ∈ iteratedFaces v 0 ↔ s.Nonempty ∧ s ⊆ Finset.univ.image v := by
  classical
  constructor
  · rintro ⟨p, hp, A, hA, rfl⟩
    have hp0 : p = [] := List.length_eq_zero_iff.mp hp
    subst p
    exact ⟨hA.image _, Finset.image_mono _ (Finset.subset_univ _)⟩
  · rintro ⟨hs, hsub⟩
    obtain ⟨A, _, hA⟩ := Finset.subset_image_iff.mp hsub
    refine ⟨[], rfl, A, ?_, hA.symm⟩
    exact Finset.image_nonempty.mp (hA.symm ▸ hs)

/-- Equal-depth barycentric descendant cells meet in the convex hull of common vertices.
Source: Schultz, Mathematics 246A §I.2 Theorem 4 and proof pp.23–25, with
Mathematics 205B §IV.2 Lemma 6 and its written gluing proof p.51.

At depth zero the vertices are independent, and intersections of vertex-face hulls
are the hulls of their intersections. For one subdivision, identify each nonempty
vertex subface with a flag of original faces. Schultz's coordinate-level argument
shows that two flag hulls meet in their common barycentric vertex hull; the existing
one-step theorem gives this exact statement, also after an injective linear change
of coordinates. For the induction, attach the last permutation to each parent path.
Parents at the preceding depth already meet in a common original face. The one-step
face-trace formula, transported into each independent parent tuple, removes exactly
those flag members not contained in this shared parent face. The remaining flags
use the same actual finite vertex subsets of the shared face. Their centroids are
independent of their ambient parent or index enumeration by centroid relabeling.
They therefore give the identical subdivision of that face. If the shared face is
empty, the two child hulls are disjoint. Otherwise apply the one-step intersection
identity in this shared face to obtain the common child-vertex hull. This is exactly
Schultz Lemma 6: every point of a cross-parent intersection belongs to a common
subdivision face and hence is a convex combination of common vertices. Induction
gives the claimed inclusion at every finite depth. Same-parent paths use the
already proved independent-coordinate one-step theorem directly. Nonempty faces,
singletons, and the one-vertex simplex need no extra hypothesis.

The proof below checks the full induction. Enumerate the finite common parent
vertex set, pull it back through both independent parent tuples, and apply the
independent-coordinate one-step restriction identity. Coverage by that shared
tuple supplies the common subcomplex needed by the gluing theorem. If its hull
contains a point then the vertex set is nonempty, so enumeration loses no case. -/
theorem iteratedFaces_convexHull_inter_subset (n r : ℕ) :
    ∀ s ∈ iteratedFaces (standardVertices n) r,
      ∀ t ∈ iteratedFaces (standardVertices n) r,
      convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩
        convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆
          convexHull ℝ ((s : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ t) := by
  classical
  let : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
  induction r with
  | zero =>
    intro s hs t ht
    have hfull : Finset.univ.image (standardVertices n) ∈
        iteratedFaces (standardVertices n) 0 :=
      ⟨[], rfl, Finset.univ, Finset.univ_nonempty, rfl⟩
    have hi := iteratedFaces_affineIndependent n 0 _ hfull
    exact (hi.convexHull_inter ((iteratedFaces_zero_iff _ s).mp hs).2
      ((iteratedFaces_zero_iff _ t).mp ht).2).symm.subset
  | succ r ih =>
    cases r with
    | zero =>
      intro s hs t ht
      exact (oneStepFaces_convexHull_inter n s t hs ht).subset
    | succ r =>
      intro s hs t ht
      obtain ⟨p, hp, A, hA, rfl⟩ := hs
      obtain ⟨q, hq, T, hT, rfl⟩ := ht
      have hpne : p ≠ [] := by intro h; simp [h] at hp
      have hqne : q ≠ [] := by intro h; simp [h] at hq
      have happend : ∀ (p q : List (Equiv.Perm (Fin (n + 1))))
          (v : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1))),
          BarycentricMesh.iteratedVertices v (p ++ q) =
            BarycentricMesh.iteratedVertices (BarycentricMesh.iteratedVertices v p) q := by
        intro p
        induction p with
        | nil => intro q v; rfl
        | cons σ p ih =>
          intro q v
          exact ih q (BarycentricMesh.childVertices v σ)
      have hlin : ∀ (p : List (Equiv.Perm (Fin (n + 1))))
          (v : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1))),
          LinearIndependent ℝ v → LinearIndependent ℝ (BarycentricMesh.iteratedVertices v p) := by
        intro p
        induction p with
        | nil => intro v hv; exact hv
        | cons σ p ih =>
          intro v hv
          exact ih _ (childVertices_linearIndependent v hv σ)
      let v := BarycentricMesh.iteratedVertices (standardVertices n) p.dropLast
      let w := BarycentricMesh.iteratedVertices (standardVertices n) q.dropLast
      have hstandard : LinearIndependent ℝ (standardVertices n) := by
        exact (Pi.linearIndependent_single_one (Fin (n + 1)) ℝ).map'
          (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.toLinearMap
          (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ _).symm.injective)
      have hv : LinearIndependent ℝ v := hlin _ _ hstandard
      have hw : LinearIndependent ℝ w := hlin _ _ hstandard
      have hpv : BarycentricMesh.iteratedVertices (standardVertices n) p =
          BarycentricMesh.iteratedVertices v [p.getLast hpne] := by
        dsimp [v]
        rw [← happend, List.dropLast_concat_getLast]
      have hqw : BarycentricMesh.iteratedVertices (standardVertices n) q =
          BarycentricMesh.iteratedVertices w [q.getLast hqne] := by
        dsimp [w]
        rw [← happend, List.dropLast_concat_getLast]
      have hs : A.image (BarycentricMesh.iteratedVertices (standardVertices n) p) ∈
          iteratedFaces v 1 :=
        ⟨[p.getLast hpne], rfl, A, hA, congrArg (Finset.image · A) hpv⟩
      have ht : T.image (BarycentricMesh.iteratedVertices (standardVertices n) q) ∈
          iteratedFaces w 1 :=
        ⟨[q.getLast hqne], rfl, T, hT, congrArg (Finset.image · T) hqw⟩
      by_cases hparent : p.dropLast = q.dropLast
      · have hvw : v = w := congrArg (BarycentricMesh.iteratedVertices (standardVertices n)) hparent
        exact (oneStepFaces_convexHull_inter_of_linearIndependent v hv _ _ hs
          (hvw.symm ▸ ht)).subset
      · -- Each individual parent already has a checked one-step geometric complex.
        let localComplex (z : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)))
            (hz : LinearIndependent ℝ z) :
            Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1))) := {
          faces := iteratedFaces z 1
          isRelLowerSet_faces := fun s hs ↦
            ⟨(iteratedFaces_nonempty_down_closed z 1).1 s hs,
              fun t hts ht ↦ (iteratedFaces_nonempty_down_closed z 1).2 s hs t hts ht⟩
          indep := by
            rintro s ⟨q, _, B, _, rfl⟩
            apply (hlin q z hz).linearIndepOn_id.affineIndepOn.mono
            rw [Finset.coe_image]
            exact Set.image_subset_range _ _
          inter_subset_convexHull := fun hs ht ↦
            (oneStepFaces_convexHull_inter_of_linearIndependent z hz _ _ hs ht).subset }
        let K := localComplex v hv
        let L := localComplex w hw
        -- Induction constructs the identical subdivision of the common parent
        -- face inside both local complexes, covering their overlap.
        have hKspace : K.space = convexHull ℝ (range v) :=
          iteratedFaces_convexHull_union v 1
        have hLspace : L.space = convexHull ℝ (range w) :=
          iteratedFaces_convexHull_union w 1
        let P := Finset.univ.image v
        let Q := Finset.univ.image w
        have hP : P ∈ iteratedFaces (standardVertices n) (r + 1) := by
          refine ⟨p.dropLast, ?_, Finset.univ, Finset.univ_nonempty, rfl⟩
          simp [List.length_dropLast, hp]
        have hQ : Q ∈ iteratedFaces (standardVertices n) (r + 1) := by
          refine ⟨q.dropLast, ?_, Finset.univ, Finset.univ_nonempty, rfl⟩
          simp [List.length_dropLast, hq]
        have hparentHull := ih P hP Q hQ
        have hcover : K.space ∩ L.space ⊆ (K ⊓ L).space := by
          intro x hx
          have hxU : x ∈ convexHull ℝ ((P ∩ Q : Finset _) : Set _) := by
            rw [Finset.coe_inter]
            apply hparentHull
            simpa only [P, Q, Finset.coe_image, Finset.coe_univ, Set.image_univ,
              hKspace, hLspace, Set.mem_inter_iff] using hx
          let U := P ∩ Q
          have hUne : U.Nonempty := by
            exact Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxU⟩)
          obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hUne)
          let e : Fin (m + 1) ≃ U :=
            (finCongr (by simpa only [Fintype.card_coe] using hm.symm)).trans
              (Fintype.equivFin U).symm
          let u : Fin (m + 1) → EuclideanSpace ℝ (Fin (n + 1)) := fun i ↦ (e i).val
          have huinj : Function.Injective u := Subtype.val_injective.comp e.injective
          have huRange : range u = (U : Set _) := by
            ext y
            constructor
            · rintro ⟨i, rfl⟩
              exact (e i).property
            · intro hy
              obtain ⟨i, hi⟩ := e.surjective ⟨y, hy⟩
              exact ⟨i, congrArg Subtype.val hi⟩
          have huv (i : Fin (m + 1)) : u i ∈ range v := by
            have hi := Finset.mem_inter.mp (e i).property
            obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi.1
            exact ⟨j, hj⟩
          have huw (i : Fin (m + 1)) : u i ∈ range w := by
            have hi := Finset.mem_inter.mp (e i).property
            obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi.2
            exact ⟨j, hj⟩
          have hav (i : Fin (m + 1)) : v (Function.invFun v (u i)) = u i := by
            obtain ⟨j, hj⟩ := huv i
            rw [← hj]
            exact Function.apply_invFun_apply
          have haw (i : Fin (m + 1)) : w (Function.invFun w (u i)) = u i := by
            obtain ⟨j, hj⟩ := huw i
            rw [← hj]
            exact Function.apply_invFun_apply
          let a : Fin (m + 1) ↪ Fin (n + 1) := {
            toFun := fun i ↦ Function.invFun v (u i)
            inj' := fun i j hij ↦ huinj ((hav i).symm.trans ((congrArg v hij).trans (hav j))) }
          let b : Fin (m + 1) ↪ Fin (n + 1) := {
            toFun := fun i ↦ Function.invFun w (u i)
            inj' := fun i j hij ↦ huinj ((haw i).symm.trans ((congrArg w hij).trans (haw j))) }
          have hva : v ∘ a = u := funext hav
          have hwb : w ∘ b = u := funext haw
          have htraceK := oneStepFaces_restriction_of_linearIndependent v hv m a
          have htraceL := oneStepFaces_restriction_of_linearIndependent w hw m b
          rw [hva] at htraceK
          rw [hwb] at htraceL
          have hxu : x ∈ convexHull ℝ (range u) := huRange.symm ▸ hxU
          rw [← iteratedFaces_convexHull_union u 1] at hxu
          obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.mp hxu
          exact Geometry.SimplicialComplex.mem_space_iff.mpr
            ⟨f, ⟨(htraceK.symm.subset hf).1, (htraceL.symm.subset hf).1⟩, hxf⟩
        exact common_subcomplex_convexHull_inter_subset K L (K ⊓ L)
          (fun _ h ↦ h.1) (fun _ h ↦ h.2) hcover hs ht

end HolomorphicAnosov.BarycentricGeometry

