import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SourceCollarDeformationLaws
import HolomorphicAnosov.AlgebraicTopology.SingularCohomologyDeformationRetraction

/-!
# Cohomology of the characteristic source collar

Source: Hatcher, Algebraic Topology, Proposition 3.17 p.217, its disk-collar
excision reduction, and homotopy invariance p.201. The maps are the actual
inclusion of the boundary union and the componentwise radial deformation.
-/
open CategoryTheory Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
open SingularCochain

/-- The inclusion of the boundary union into the union of outer disk collars
induces an isomorphism on absolute singular cohomology in every degree.

Proof: the published source-collar deformation starts at the identity, ends
at the radial boundary retraction, and fixes the boundary pointwise. Apply
cohomology invariance of this deformation retraction. The actual Sigma and
subspace topologies are retained; zero-dimensional disks, empty cell families,
and the zero coefficient ring are included. Source: Hatcher p.217 and p.201. -/
theorem sourceCollar_cohomology_isIso
    (X : Type u) [TopologicalSpace X] [CWComplex (univ : Set X)]
    (R : Type u) [CommRing R] (m n : ℕ)
    (hSU : {z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m |
        z.2 ∈ cellBoundary m} ⊆ {z | (1 / 2 : ℝ) < ‖z.2.down.1‖}) :
    IsIso (cohomologyPullback R (TopCat.ofHom (ContinuousMap.inclusion hSU)) n) := by
  let i := ContinuousMap.inclusion hSU
  let r := sourceBoundaryRetraction X m
  have hr : TopCat.ofHom i ≫ TopCat.ofHom r = 𝟙 _ := by
    ext a : 1
    apply Subtype.ext
    have h := (sourceCollarDeformation_laws X m (i a)).2.2 1 a.2
    exact (sourceCollarDeformation_laws X m (i a)).2.1.symm.trans
      (congrArg Subtype.val h)
  let H : TopCat.Homotopy (𝟙 _) (TopCat.ofHom r ≫ TopCat.ofHom i) :=
    { toFun := sourceCollarDeformation X m
      continuous_toFun := (sourceCollarDeformation X m).continuous
      map_zero_left := fun z ↦ (sourceCollarDeformation_laws X m z).1
      map_one_left := fun z ↦ Subtype.ext (sourceCollarDeformation_laws X m z).2.1 }
  exact cohomologyPullback_isIso_of_deformationRetraction R
    (TopCat.ofHom i) (TopCat.ofHom r) hr H n

end HolomorphicAnosov.CharacteristicCellComparison
