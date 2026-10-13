import HolomorphicAnosov.Topology.Cubical.CellwiseHomologyInjectiveG15
import HolomorphicAnosov.Topology.Cubical.SubcomplexCWStructureG15

noncomputable section
open CategoryTheory CategoryTheory.Limits Set _root_.Topology
open HolomorphicAnosov.CharacteristicCellComparison
namespace HolomorphicAnosov.Cubical

lemma nativeSubcomplex_skeleton_subset {X : Type} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] (E : RelCWComplex.Subcomplex C) (q : ℕ) :
    (CWComplex.skeleton (E : Set X) q : Set X) ⊆ CWComplex.skeleton C q := by
  intro x hx
  obtain ⟨n, hn, i, hi⟩ := CWComplex.mem_skeleton_iff.mp hx
  exact CWComplex.mem_skeleton_iff.mpr ⟨n, hn, i.val, hi⟩

/-- A native subcomplex contained in the q-skeleton equals its own q-skeleton.
Each point lies in an open selected cell and an ambient open cell of degree at
most q. Disjointness of distinct open cells forces the two labels to agree. -/
lemma nativeSubcomplex_skeleton_eq {X : Type} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] (E : RelCWComplex.Subcomplex C) (q : ℕ)
    (hE : (E : Set X) ⊆ CWComplex.skeleton C q) :
    (CWComplex.skeleton (E : Set X) q : Set X) = E := by
  apply Subset.antisymm (RelCWComplex.Subcomplex.subset_complex _)
  intro x hx
  have hopen : x ∈ ⋃ (n : ℕ) (i : RelCWComplex.cell (E : Set X) n),
      RelCWComplex.openCell n i := by rw [CWComplex.iUnion_openCell_eq_complex]; exact hx
  obtain ⟨n, i, hi⟩ := by simpa only [mem_iUnion] using hopen
  obtain ⟨m, hm, j, hj⟩ := CWComplex.mem_skeleton_iff.mp (hE hx)
  have he : (⟨n, i.val⟩ : Σ n, RelCWComplex.cell C n) = ⟨m, j⟩ :=
    RelCWComplex.eq_of_not_disjoint_openCell (by
      intro hd
      exact Set.disjoint_left.mp hd hi hj)
  have hnm : n = m := congrArg Sigma.fst he
  exact CWComplex.mem_skeleton_iff.mpr ⟨n, hnm ▸ hm, i, hi⟩

/-- The transported carrier skeleton is homeomorphic to the original ambient skeleton. -/
def cwCarrierSkeletonHomeomorph {X : Type} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] (c0 : C) (q : ℕ) :
    letI := cwCarrierStructureG6 C c0
    Skeleton C q ≃ₜ (CWComplex.skeleton C q : Set X) := by
  letI := cwCarrierStructureG6 C c0
  let hs := cwCarrier_skeleton_eq C c0 q
  exact {
    toFun := fun x ↦ ⟨x.val.val,
      (congrArg (fun S : Set C ↦ x.val ∈ S) hs).mp x.property⟩
    invFun := fun x ↦ ⟨⟨x.val, (CWComplex.skeleton C q).subset_complex x.property⟩,
      (congrArg (fun S : Set C ↦
        (⟨x.val, (CWComplex.skeleton C q).subset_complex x.property⟩ : C) ∈ S) hs).mpr
        x.property⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

/-- Inclusion of a native finite CW subcomplex into the ambient q-skeleton is
injective on q-homology when the subcomplex is contained in that skeleton.
Source: Hatcher Lemma 2.34 and Theorem 2.35, pp.137–141. The inherited cell
labels are literal subtype inclusions, and their characteristic maps agree. -/
theorem nativeSubcomplex_homology_mono {X : Type} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] [CWComplex.Finite C]
    (E : RelCWComplex.Subcomplex C) (q : ℕ) (hq : 0 < q)
    (hE : (E : Set X) ⊆ CWComplex.skeleton C q) :
    Mono (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj
      (ModuleCat.of ℚ ℚ)).map (TopCat.ofHom (ContinuousMap.inclusion hE))) := by
  classical
  by_cases hn : Nonempty (E : Set X)
  · obtain ⟨e0⟩ := hn
    let c0 : C := ⟨e0.val, E.subset_complex e0.property⟩
    let := cwCarrierStructureG6 C c0
    let := cwCarrier_finite C c0
    let := cwCarrierStructureG6 (E : Set X) e0
    let := cwCarrier_finite (E : Set X) e0
    let eE : TopCat.of (Skeleton (E : Set X) q) ≅
        TopCat.of (CWComplex.skeleton (E : Set X) q : Set X) :=
      TopCat.isoOfHomeo (cwCarrierSkeletonHomeomorph (E : Set X) e0 q)
    let eC : TopCat.of (Skeleton C q) ≅
        TopCat.of (CWComplex.skeleton C q : Set X) :=
      TopCat.isoOfHomeo (cwCarrierSkeletonHomeomorph C c0 q)
    let hEC := nativeSubcomplex_skeleton_subset C E q
    let f : TopCat.of (Skeleton (E : Set X) q) ⟶ TopCat.of (Skeleton C q) :=
      eE.hom ≫ TopCat.ofHom (ContinuousMap.inclusion hEC) ≫ eC.inv
    have hf : MapsTo f (lowerSkeleton (E : Set X) q) (lowerSkeleton C q) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      intro x hx
      change x.val ∈ (CWComplex.skeleton (univ : Set (E : Set X)) m : Set (E : Set X)) at hx
      rw [cwCarrier_skeleton_eq (E : Set X) e0 m] at hx
      change (f x).val ∈ (CWComplex.skeleton (univ : Set C) m : Set C)
      rw [cwCarrier_skeleton_eq C c0 m]
      exact nativeSubcomplex_skeleton_subset C E m hx
    let j : RelCWComplex.cell (univ : Set (E : Set X)) q →
        RelCWComplex.cell (univ : Set C) q := Subtype.val
    have hj : Function.Injective j := Subtype.val_injective
    have hchar : ∀ i z, f (characteristicCell (E : Set X) q i z) =
        characteristicCell C q (j i) z := by
      intro i z
      apply Subtype.ext
      apply Subtype.ext
      change (cwCarrierMapG6 (E : Set X) e0 q i z.down.val).val =
        (cwCarrierMapG6 C c0 q i.val z.down.val).val
      rw [cwCarrierMapG6_coe (E : Set X) e0 q i z.down.property,
        cwCarrierMapG6_coe C c0 q i.val z.down.property]
      rfl
    have hi := skeleton_homology_mono_of_characteristic (E : Set X) C q hq f hf j hj hchar
    let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj (ModuleCat.of ℚ ℚ)
    have hs := nativeSubcomplex_skeleton_eq C E q hE
    let eFull : TopCat.of (CWComplex.skeleton (E : Set X) q : Set X) ≅
        TopCat.of (E : Set X) := TopCat.isoOfHomeo (Homeomorph.setCongr hs)
    have he : TopCat.ofHom (ContinuousMap.inclusion hE) =
        eFull.inv ≫ eE.inv ≫ f ≫ eC.hom := by
      ext x : 1
      rfl
    change Mono (H.map _)
    rw [he, H.map_comp, H.map_comp, H.map_comp]
    infer_instance
  · have : IsEmpty (E : Set X) := not_nonempty_iff.mp hn
    exact (singular_homology_isZero_of_isEmpty (TopCat.of (E : Set X))
      (ModuleCat.of ℚ ℚ) q).mono _

end HolomorphicAnosov.Cubical

