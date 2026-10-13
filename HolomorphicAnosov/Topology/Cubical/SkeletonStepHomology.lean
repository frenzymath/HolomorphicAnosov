import HolomorphicAnosov.Topology.Cubical.CharacteristicHomologyComparison
import HolomorphicAnosov.Topology.Cubical.SigmaRelativeHomology

open Set CategoryTheory CategoryTheory.Limits _root_.Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace HolomorphicAnosov.CharacteristicCellComparison

/-- Hatcher Lemma 2.34(a), pp.137–138. Characteristic excision identifies the
skeletal relative homology with the relative homology of the disk-boundary
union; finite disjoint union decomposition transfers vanishing of one disk pair. -/
theorem skeleton_relative_homology_isZero
    (X : Type) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
    [CWComplex.Finite (univ : Set X)] (m : ℕ) (R : ModuleCat ℚ) (n : ℕ)
    (hz : IsZero ((singularSubspacePair (TopCat.of (CellDisk.{0} m))
      (cellBoundary m)).homology R n)) :
    IsZero ((singularSubspacePair (TopCat.of (Skeleton X m))
      (lowerSkeleton X m)).homology R n) := by
  let : Finite (RelCWComplex.cell (univ : Set X) m) :=
    RelCWComplex.FiniteType.finite_cell m
  let := Fintype.ofFinite (RelCWComplex.cell (univ : Set X) m)
  let Φ : TopCat.of (Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{0} m) ⟶
      TopCat.of (Skeleton X m) := TopCat.ofHom
    ⟨fun z ↦ characteristicCell X m z.1 z.2,
      continuous_sigma fun i ↦ (characteristicCell X m i).continuous⟩
  let f := singularSubspacePairMap Φ {z | z.2 ∈ cellBoundary m}
    (lowerSkeleton X m) (fun z hz ↦ characteristicCell_mapsTo X m z.1 hz)
  have : IsIso (SSetPair.homologyMap f R n) :=
    characteristic_relative_homology_isIso X m R n
  exact (Cubical.sigmaSingularSubspaceHomology_isZero
    (ι := RelCWComplex.cell (univ : Set X) m) _ _ R n hz).of_iso
      (asIso (SSetPair.homologyMap f R n)).symm

lemma singularSubspace_homology_epi_of_relative_isZero
    (X : TopCat) (A : Set X) (R : ModuleCat ℚ) (n : ℕ)
    (hz : IsZero ((singularSubspacePair X A).homology R n)) :
    Epi (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) n).obj R).map
      (singularSubspaceInclusion X A)) := by
  exact ((singularSubspacePair X A).homology_exact₂ R n).epi_f_iff.mpr
    (hz.eq_zero_of_tgt _)


/-- The lower part of the next skeleton is the previous skeleton with its original topology. -/
def lowerSkeletonHomeomorph (X : Type) [TopologicalSpace X] [T2Space X]
    [CWComplex (univ : Set X)] (m : ℕ) :
    lowerSkeleton X (m + 1) ≃ₜ Skeleton X m := {
  toFun := fun x ↦ ⟨x.val.val, x.property⟩
  invFun := fun x ↦ ⟨⟨x.val, RelCWComplex.skeletonLT_mono
    (C := (univ : Set X)) (by exact_mod_cast (Nat.le_succ (m + 1))) x.property⟩, x.property⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop }

def skeletonStepInclusion (X : Type) [TopologicalSpace X] [T2Space X]
    [CWComplex (univ : Set X)] (m : ℕ) :
    TopCat.of (Skeleton X m) ⟶ TopCat.of (Skeleton X (m + 1)) :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.val, RelCWComplex.skeletonLT_mono
    (C := (univ : Set X)) (by exact_mod_cast (Nat.le_succ (m + 1))) x.property⟩,
    by fun_prop⟩

/-- Hatcher Lemma 2.34(b). The relative vanishing hypothesis and pair exactness
make the preceding-skeleton inclusion surjective on homology. -/
theorem skeletonStep_homology_epi
    (X : Type) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
    [CWComplex.Finite (univ : Set X)] (m : ℕ) (R : ModuleCat ℚ) (n : ℕ)
    (hz : IsZero ((singularSubspacePair (TopCat.of (CellDisk.{0} (m + 1)))
      (cellBoundary (m + 1))).homology R n)) :
    Epi (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) n).obj R).map
      (skeletonStepInclusion X m)) := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) n).obj R
  let e : TopCat.of (lowerSkeleton X (m + 1)) ≅ TopCat.of (Skeleton X m) :=
    TopCat.isoOfHomeo (lowerSkeletonHomeomorph X m)
  have := singularSubspace_homology_epi_of_relative_isZero _ _ R n
    (skeleton_relative_homology_isZero X (m + 1) R n hz)
  have heq : skeletonStepInclusion X m =
      e.inv ≫ singularSubspaceInclusion (TopCat.of (Skeleton X (m + 1)))
        (lowerSkeleton X (m + 1)) := rfl
  change Epi (F.map _)
  rw [heq, F.map_comp]
  infer_instance

end HolomorphicAnosov.CharacteristicCellComparison

