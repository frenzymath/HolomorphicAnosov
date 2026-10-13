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

namespace HolomorphicAnosov

universe u v

/-- Closed pasting for the two pieces of Hatcher's skeletal endpoint target
(Proposition 0.16, p.15). The dependent choice uses the covering property, so no
nonempty codomain is needed. A closed-set preimage is the union of the two closed
images of the restricted preimages, proving continuity for arbitrary codomains. -/
theorem cw_glue_two_closed
    {Z : Type*} {Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y]
    (s t : Set Z) (hs : IsClosed s) (ht : IsClosed t)
    (hcover : ∀ z : Z, z ∈ s ∨ z ∈ t)
    (f : C(s, Y)) (g : C(t, Y))
    (hagree : ∀ (z : Z) (hzs : z ∈ s) (hzt : z ∈ t), f ⟨z, hzs⟩ = g ⟨z, hzt⟩) :
    ∃ k : C(Z, Y),
      (∀ (z : Z) (hz : z ∈ s), k z = f ⟨z, hz⟩) ∧
      (∀ (z : Z) (hz : z ∈ t), k z = g ⟨z, hz⟩) := by
  classical
  let k (z : Z) : Y := if hz : z ∈ s then f ⟨z, hz⟩
    else g ⟨z, (hcover z).resolve_left hz⟩
  have hks (z : Z) (hz : z ∈ s) : k z = f ⟨z, hz⟩ := by
    simp only [k, dite_eq_left hz]
  have hkt (z : Z) (hz : z ∈ t) : k z = g ⟨z, hz⟩ := by
    by_cases hzs : z ∈ s
    · exact (hks z hzs).trans (hagree z hzs hz)
    · simp only [k, dite_eq_right hzs]
  have hk : Continuous k := by
    rw [continuous_iff_isClosed]
    intro A hA
    have hpre : k ⁻¹' A =
        (Subtype.val '' (f ⁻¹' A) : Set Z) ∪ (Subtype.val '' (g ⁻¹' A) : Set Z) := by
      ext z
      constructor
      · intro hz
        rcases hcover z with hzs | hzt
        · refine Or.inl ⟨⟨z, hzs⟩, ?_, rfl⟩
          change f ⟨z, hzs⟩ ∈ A
          rw [← hks z hzs]
          exact hz
        · refine Or.inr ⟨⟨z, hzt⟩, ?_, rfl⟩
          change g ⟨z, hzt⟩ ∈ A
          rw [← hkt z hzt]
          exact hz
      · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
        · change k w.val ∈ A
          rw [hks w.val w.property]
          exact hw
        · change k w.val ∈ A
          rw [hkt w.val w.property]
          exact hw
    rw [hpre]
    exact (hs.isClosedMap_subtype_val _ (hA.preimage f.continuous)).union
      (ht.isClosedMap_subtype_val _ (hA.preimage g.continuous))
  exact ⟨⟨k, hk⟩, hks, hkt⟩

end HolomorphicAnosov
