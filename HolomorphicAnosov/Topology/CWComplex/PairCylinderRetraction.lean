import HolomorphicAnosov.Topology.EuclideanDiskUnitCube
import HolomorphicAnosov.Topology.CWComplex.CharacteristicContinuity
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Homotopy.Basic
import HolomorphicAnosov.Topology.CWComplex.PairExtensionOfRetraction
import HolomorphicAnosov.Topology.CWComplex.RadialScaleBounds
import HolomorphicAnosov.Topology.CWComplex.RadialHeightBounds
import HolomorphicAnosov.Topology.CWComplex.RadialNormBound
import HolomorphicAnosov.Topology.CWComplex.RadialProjection
import HolomorphicAnosov.Topology.CWComplex.ContinuousRadialProjection
import HolomorphicAnosov.Topology.CWComplex.RadialBottom
import HolomorphicAnosov.Topology.CWComplex.RadialSide
import HolomorphicAnosov.Topology.CWComplex.RadialBoundaryTarget
import HolomorphicAnosov.Topology.CWComplex.RadialCharacteristicFrontier
import HolomorphicAnosov.Topology.CWComplex.RadialCharacteristicTarget
import HolomorphicAnosov.Topology.CWComplex.CompatibleSkeleta
import HolomorphicAnosov.Topology.CWComplex.SubtypeGlueCharacteristicDoublePrisms
import HolomorphicAnosov.Topology.CWComplex.CellBoundaryNeSameDimInterior
import HolomorphicAnosov.Topology.CWComplex.RadialSameDimCompatible
import HolomorphicAnosov.Topology.CWComplex.PrismDeformation
import HolomorphicAnosov.Topology.CWComplex.ContinuousPrismDeformation
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationZero
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationOne
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationFixed
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationBottom
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationSide
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationSameDimCompatible
import HolomorphicAnosov.Topology.CWComplex.CellInLowerSkeletonBoundary
import HolomorphicAnosov.Topology.CWComplex.CellInSubcomplexBoundary
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationLowerCellCompatible
import HolomorphicAnosov.Topology.CWComplex.SelectedCellStage
import HolomorphicAnosov.Topology.CWComplex.SelectedCellStageProperties
import HolomorphicAnosov.Topology.CWComplex.GlueTwoClosed
import HolomorphicAnosov.Topology.CWComplex.ExtendLowerRetraction
import HolomorphicAnosov.Topology.CWComplex.RetractionSkeletalStep
import HolomorphicAnosov.Topology.CWComplex.CompatibleSkeletalRetractions

namespace HolomorphicAnosov

universe u v

/-- The global endpoint retraction in Hatcher's Proposition 0.16, pp.14–15.
The compatible finite retractions descend through the original characteristic
prisms, so continuity is for the ordinary product topology. Every point belongs
to a finite skeleton, which transfers bottom and `B` fixedness to the global
map. Fixedness supplies an explicit preimage for every point of the target,
including without any nonemptiness assumption. -/
theorem cw_pair_cylinder_retraction
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (B : Topology.CWComplex.Subcomplex (Set.univ : Set X)) :
    ∃ r : C(unitInterval × X, {p : unitInterval × X | p.1 = 0 ∨ p.2 ∈ (B : Set X)}),
      (∀ x : X, (r (0, x)).val = (0, x)) ∧
      (∀ (t : unitInterval) (b : (B : Set X)), (r (t, b.val)).val = (t, b.val)) ∧
      Function.Surjective r := by
  obtain ⟨R, hRbottom, hRside, hRcompat⟩ := cw_compatible_skeletal_retractions B
  obtain ⟨r, hr⟩ := cw_prism_of_compatible_skeleta R hRcompat
  have hcover (x : X) : ∃ n : ℕ,
      x ∈ (Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X) := by
    have hx : x ∈ ⋃ n : ℕ,
        (Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X) := by
      rw [Topology.CWComplex.iUnion_skeleton_eq_complex]
      exact Set.mem_univ _
    exact Set.mem_iUnion.mp hx
  have hbottom (x : X) : (r (0, x)).val = (0, x) := by
    obtain ⟨n, hx⟩ := hcover x
    exact (congrArg Subtype.val (hr n 0 ⟨x, hx⟩)).trans (hRbottom n ⟨x, hx⟩)
  have hside (t : unitInterval) (b : (B : Set X)) :
      (r (t, b.val)).val = (t, b.val) := by
    obtain ⟨n, hx⟩ := hcover b.val
    exact (congrArg Subtype.val (hr n t ⟨b.val, hx⟩)).trans
      (hRside n t ⟨b.val, hx⟩ b.property)
  refine ⟨r, hbottom, hside, ?_⟩
  intro p
  refine ⟨p.val, Subtype.ext ?_⟩
  change (r (p.val.1, p.val.2)).val = (p.val.1, p.val.2)
  rcases p.property with hp | hp
  · rw [hp]
    exact hbottom p.val.2
  · exact hside p.val.1 ⟨p.val.2, hp⟩

end HolomorphicAnosov
