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

namespace HolomorphicAnosov

universe u v

/-- One finite skeletal step in the endpoint-only form of Hatcher's
Proposition 0.16, p.15. Compose the selected-cell endpoint with the lower
retraction extended by the identity. The new retraction fixes the bottom and
`B`, and its restriction to the previous skeleton is exactly the old retraction.
No choices of characteristic representatives enter the compatibility equation. -/
theorem cw_retraction_skeletal_step
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (B : Topology.CWComplex.Subcomplex (Set.univ : Set X)) (n : ℕ)
    (R : C(unitInterval ×
        (Topology.CWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X),
      {p : unitInterval × X | p.1 = 0 ∨ p.2 ∈ (B : Set X)}))
    (hRbottom : ∀ x, (R (0, x)).val = (0, x.val))
    (hRside : ∀ t x, x.val ∈ (B : Set X) → (R (t, x)).val = (t, x.val)) :
    let S := Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞)
    ∃ R' : C(unitInterval × (S : Set X),
        {p : unitInterval × X | p.1 = 0 ∨ p.2 ∈ (B : Set X)}),
      (∀ x, (R' (0, x)).val = (0, x.val)) ∧
      (∀ t x, x.val ∈ (B : Set X) → (R' (t, x)).val = (t, x.val)) ∧
      (∀ (t : unitInterval)
        (x : (Topology.CWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X))
        (hx : x.val ∈ (S : Set X)), R' (t, ⟨x.val, hx⟩) = R (t, x)) := by
  let S := Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞)
  let L : Set X := Topology.CWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞)
  let E : Set (unitInterval × X) := {p | p.1 = 0 ∨ p.2 ∈ L ∨ p.2 ∈ (B : Set X)}
  obtain ⟨K, hKlower, hKfixed⟩ := cw_extend_lower_retraction B L
    (Topology.CWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞)).closed R hRbottom hRside
  obtain ⟨H, _, _, hbottom, hfixed, hend⟩ := cw_selected_cell_stage_properties B n
  have hE (q : unitInterval × (S : Set X)) : H (1, q) ∈ E := by
    rcases hend q.1 q.2 with hbot | hother
    · exact Or.inl hbot.1
    · rcases hother.2 with hlower | hB
      · exact Or.inr (Or.inl hlower)
      · exact Or.inr (Or.inr hB.1)
  let endpoint : C(unitInterval × (S : Set X), E) :=
    ⟨fun q ↦ ⟨H (1, q), hE q⟩,
      (H.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk hE⟩
  refine ⟨K.comp endpoint, ?_, ?_, ?_⟩
  · intro x
    have he : endpoint (0, x) = ⟨(0, x.val), Or.inl rfl⟩ :=
      Subtype.ext (hbottom 1 x)
    change (K (endpoint (0, x))).val = (0, x.val)
    rw [he]
    exact hKfixed ⟨(0, x.val), Or.inl rfl⟩
  · intro t x hx
    have he : endpoint (t, x) = ⟨(t, x.val), Or.inr (Or.inr hx)⟩ :=
      Subtype.ext (hfixed 1 t x (Or.inl hx))
    change (K (endpoint (t, x))).val = (t, x.val)
    rw [he]
    exact hKfixed ⟨(t, x.val), Or.inr hx⟩
  · intro t x hx
    have he : endpoint (t, ⟨x.val, hx⟩) =
        ⟨(t, x.val), Or.inr (Or.inl x.property)⟩ :=
      Subtype.ext (hfixed 1 t ⟨x.val, hx⟩ (Or.inr x.property))
    change K (endpoint (t, ⟨x.val, hx⟩)) = R (t, x)
    rw [he]
    exact hKlower t x

end HolomorphicAnosov
