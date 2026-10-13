import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollarStrongDeformationRetraction
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.LowerSkeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollar
import HolomorphicAnosov.AlgebraicTopology.SingularCohomologyDeformationRetraction
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition

/-!
# Absolute cohomology of the characteristic skeleton collar

Source: Hatcher, Algebraic Topology, homotopy invariance p.201, Proposition 2.22
p.124, and the characteristic-cell excision reduction in Proposition 3.17 p.217.
DAG: topo.characteristic_skeleton_collar_cohomology_g5.
-/
open CategoryTheory
open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
open SingularCochain

/-- Inclusion of the lower skeleton into its actual open collar induces an
isomorphism on absolute singular cohomology in every degree over any
commutative ring. The inclusion uses any proof of the same subset relation.

Proof: obtain the continuous radial retraction and its homotopy from the proved
strong deformation retraction. Its pointwise retraction identity is an equality
of continuous maps by extensionality. Forget the stationary condition on the
homotopy and apply absolute cohomology invariance of a deformation retraction.
This includes m = 0, empty lower skeletons, and empty collars. -/
theorem skeletonCollar_cohomology_isIso
    (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
    [CWComplex.Finite (univ : Set X)] (R : Type u) [CommRing R] (m n : ℕ)
    (hAU : lowerSkeleton X m ⊆ skeletonCollar X m) :
    IsIso (cohomologyPullback R (TopCat.ofHom (ContinuousMap.inclusion hAU)) n) := by
  obtain ⟨hAU', r, hr, ⟨H⟩⟩ := skeletonCollar_strongDeformationRetraction X m
  apply cohomologyPullback_isIso_of_deformationRetraction R
    (TopCat.ofHom (ContinuousMap.inclusion hAU)) (TopCat.ofHom r) _
    (show TopCat.Homotopy (𝟙 (TopCat.of ↥(skeletonCollar X m)))
      (TopCat.ofHom r ≫ TopCat.ofHom (ContinuousMap.inclusion hAU)) from H.toHomotopy) n
  ext a : 1
  exact hr a

end HolomorphicAnosov.CharacteristicCellComparison
