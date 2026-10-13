import HolomorphicAnosov.Topology.Cubical.SkeletonStepHomology
import HolomorphicAnosov.Topology.Homology.SphereHighDegreeG15

noncomputable section
open Set CategoryTheory CategoryTheory.Limits _root_.Topology
namespace HolomorphicAnosov.CharacteristicCellComparison

variable (X : Type) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
    [CWComplex.Finite (univ : Set X)]

/-- The relative homology of successive finite skeleta vanishes above the cell dimension.
Hatcher Lemma 2.34(a): the characteristic disk pairs compute the relative homology;
there are finitely many disks and each has zero homology above its dimension. -/
theorem skeletonPair_high_degree (m q : ℕ) (hq : m < q) :
    IsZero ((singularSubspacePair (TopCat.of (Skeleton X m))
      (lowerSkeleton X m)).homology (ModuleCat.of ℚ ℚ) q) := by
  exact skeleton_relative_homology_isZero X m (ModuleCat.of ℚ ℚ) q
    (cellDisk_high_degree_rational m q hq)

/-- Each finite skeleton has no homology above its dimension. Hatcher Lemma 2.34(b).
Induct on the skeleton dimension. The zero-skeleton pair has empty lower space;
at the successor step exactness puts absolute homology between the previous
skeleton's homology and the relative disk-pair homology, both zero. -/
theorem skeleton_high_degree (m q : ℕ) (hq : m < q) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj
      (ModuleCat.of ℚ ℚ)).obj (TopCat.of (Skeleton X m))) := by
  induction m with
  | zero =>
    let P := singularSubspacePair (TopCat.of (Skeleton X 0)) (lowerSkeleton X 0)
    have : IsEmpty (lowerSkeleton X 0) := ⟨fun x ↦ by
      have hx := x.property
      change x.val.val ∈ (CWComplex.skeletonLT (univ : Set X) 0 : Set X) at hx
      simp only [CWComplex.skeletonLT_zero_eq_empty, mem_empty_iff_false] at hx
    ⟩
    exact (P.homology_exact₂ (ModuleCat.of ℚ ℚ) q).isZero_of_both_isZero
      (singular_homology_isZero_of_isEmpty (TopCat.of (lowerSkeleton X 0)) _ q)
      (skeletonPair_high_degree X 0 q hq)
  | succ m ih =>
    let R := ModuleCat.of ℚ ℚ
    let P := singularSubspacePair (TopCat.of (Skeleton X (m + 1))) (lowerSkeleton X (m + 1))
    let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj R
    have hz : IsZero (P.left.homology R q) :=
      (ih (by omega)).of_iso (F.mapIso (TopCat.isoOfHomeo (X := TopCat.of (lowerSkeleton X (m + 1)))
        (Y := TopCat.of (Skeleton X m)) (lowerSkeletonHomeomorph X m)))
    exact (P.homology_exact₂ R q).isZero_of_both_isZero hz
      (skeletonPair_high_degree X (m + 1) q hq)

/-- A finite CW space with no cells above N has zero homology above N.
Every point belongs to an open cell; the dimension bound places that cell in
the N-skeleton, which is therefore the entire space. Apply the skeletal bound.
Source: Hatcher Lemma 2.34(b), pp.137–138. -/
theorem finiteCW_high_degree (N q : ℕ)
    (hcells : ∀ n, N < n → IsEmpty (RelCWComplex.cell (univ : Set X) n)) (hq : N < q) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj
      (ModuleCat.of ℚ ℚ)).obj (TopCat.of X)) := by
  have hfull : (CWComplex.skeletonLT (univ : Set X) (N + 1) : Set X) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n),
        RelCWComplex.openCell n i := by rw [CWComplex.iUnion_openCell_eq_complex]; trivial
    obtain ⟨n, i, hi⟩ := by simpa only [mem_iUnion] using hx
    have hn : n ≤ N := by
      by_contra hn
      exact (hcells n (by omega)).false i
    apply CWComplex.mem_skeletonLT_iff.mpr
    exact ⟨n, by exact_mod_cast (by omega : n < N + 1), i, hi⟩
  let e : Skeleton X N ≃ₜ X := (Homeomorph.setCongr hfull).trans (Homeomorph.Set.univ X)
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj (ModuleCat.of ℚ ℚ)
  exact (skeleton_high_degree X N q hq).of_iso
    (F.mapIso (TopCat.isoOfHomeo (X := TopCat.of (Skeleton X N)) (Y := TopCat.of X) e)).symm

end HolomorphicAnosov.CharacteristicCellComparison
