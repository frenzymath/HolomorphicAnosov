import HolomorphicAnosov.Topology.Cubical.SkeletonStepHomology
import HolomorphicAnosov.Topology.Homology.SphereHighDegreeG15

open Set CategoryTheory CategoryTheory.Limits _root_.Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace HolomorphicAnosov.CharacteristicCellComparison

lemma singularSubspace_homology_mono_of_relative_isZero
    (X : TopCat) (A : Set X) (R : ModuleCat ℚ) (n : ℕ)
    (hz : IsZero ((singularSubspacePair X A).homology R (n + 1))) :
    Mono (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) n).obj R).map
      (singularSubspaceInclusion X A)) := by
  exact ((singularSubspacePair X A).homology_exact₁ R (n + 1) n).mono_g
    (hz.eq_zero_of_src _)

/-- Hatcher Lemma 2.34(b): below the attaching-cell degree minus one, the
relative group in the connecting-map source is zero, so the skeleton inclusion
is injective on homology. -/
theorem skeletonStep_homology_mono
    (X : Type) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
    [CWComplex.Finite (univ : Set X)] (m n : ℕ) (hn : n < m) :
    Mono (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) n).obj
      (ModuleCat.of ℚ ℚ)).map (skeletonStepInclusion X m)) := by
  let R := ModuleCat.of ℚ ℚ
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) n).obj R
  let e : TopCat.of (lowerSkeleton X (m + 1)) ≅ TopCat.of (Skeleton X m) :=
    TopCat.isoOfHomeo (lowerSkeletonHomeomorph X m)
  have := singularSubspace_homology_mono_of_relative_isZero _ _ R n
    (skeleton_relative_homology_isZero X (m + 1) R (n + 1)
      (cellDisk_low_degree_rational (m + 1) (n + 1) (by omega)))
  have heq : skeletonStepInclusion X m =
      e.inv ≫ singularSubspaceInclusion (TopCat.of (Skeleton X (m + 1)))
        (lowerSkeleton X (m + 1)) := rfl
  change Mono (F.map _)
  rw [heq, F.map_comp]
  infer_instance

/-- Later attaching cells preserve vanishing in lower degrees. -/
theorem skeleton_homology_isZero_of_later
    (X : Type) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
    [CWComplex.Finite (univ : Set X)] (m k n : ℕ) (hn : n < m)
    (hz : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) n).obj
      (ModuleCat.of ℚ ℚ)).obj (TopCat.of (Skeleton X (m + k))))) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) n).obj
      (ModuleCat.of ℚ ℚ)).obj (TopCat.of (Skeleton X m))) := by
  induction k generalizing m with
  | zero => exact hz
  | succ k ih =>
    have he : m + 1 + k = m + (k + 1) := by omega
    have hz' := ih (m + 1) (by omega) (he.symm ▸ hz)
    have := skeletonStep_homology_mono X m n hn
    exact IsZero.of_mono
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) n).obj
        (ModuleCat.of ℚ ℚ)).map (skeletonStepInclusion X m)) hz'

/-- A full later skeleton identifies its homology with that of the entire space. -/
theorem skeleton_homology_isZero_of_full
    (X : Type) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
    [CWComplex.Finite (univ : Set X)] (m N n : ℕ) (hn : n < m) (hm : m ≤ N)
    (hfull : (CWComplex.skeletonLT (univ : Set X) (N + 1) : Set X) = univ)
    (hz : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) n).obj
      (ModuleCat.of ℚ ℚ)).obj (TopCat.of X))) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) n).obj
      (ModuleCat.of ℚ ℚ)).obj (TopCat.of (Skeleton X m))) := by
  let e : Skeleton X N ≃ₜ X := (Homeomorph.setCongr hfull).trans (Homeomorph.Set.univ X)
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) n).obj (ModuleCat.of ℚ ℚ)
  have ht : IsZero (F.obj (TopCat.of (Skeleton X N))) := hz.of_iso
    (F.mapIso (TopCat.isoOfHomeo (X := TopCat.of (Skeleton X N)) (Y := TopCat.of X) e))
  apply skeleton_homology_isZero_of_later X m (N - m) n hn
  have he : m + (N - m) = N := by omega
  rw [he]
  exact ht

end HolomorphicAnosov.CharacteristicCellComparison
