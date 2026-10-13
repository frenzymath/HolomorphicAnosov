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

namespace HolomorphicAnosov

universe u v

/-- Extend a lower-skeleton retraction by the identity over the entire bottom
and `B` cylinder. This is the closed-pasting step between adjacent skeletal
endpoints in Hatcher's Proposition 0.16, p.15. On the overlap, the lower
retraction already fixes the bottom and `B`, so the two maps agree exactly.
The output equations supply both adjacent-stage compatibility and fixedness
when this map is composed with a selected-cell endpoint. -/
theorem cw_extend_lower_retraction
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (B : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (L : Set X) (hL : IsClosed L)
    (R : C(unitInterval × L, {p : unitInterval × X | p.1 = 0 ∨ p.2 ∈ (B : Set X)}))
    (hRbottom : ∀ x : L, (R (0, x)).val = (0, x.val))
    (hRside : ∀ (t : unitInterval) (x : L), x.val ∈ (B : Set X) →
      (R (t, x)).val = (t, x.val)) :
    ∃ K : C({p : unitInterval × X | p.1 = 0 ∨ p.2 ∈ L ∨ p.2 ∈ (B : Set X)},
        {p : unitInterval × X | p.1 = 0 ∨ p.2 ∈ (B : Set X)}),
      (∀ (t : unitInterval) (x : L),
        K ⟨(t, x.val), Or.inr (Or.inl x.property)⟩ = R (t, x)) ∧
      (∀ p : {p : unitInterval × X | p.1 = 0 ∨ p.2 ∈ (B : Set X)},
        (K ⟨p.val, p.property.elim Or.inl (fun hb ↦ Or.inr (Or.inr hb))⟩).val = p.val) := by
  let C₀ : Set (unitInterval × X) := {p | p.1 = 0 ∨ p.2 ∈ (B : Set X)}
  let E : Set (unitInterval × X) := {p | p.1 = 0 ∨ p.2 ∈ L ∨ p.2 ∈ (B : Set X)}
  change ∃ K : C(E, C₀), _
  let lower : Set E := {p | p.val.2 ∈ L}
  let fixed : Set E := {p | p.val.1 = 0 ∨ p.val.2 ∈ (B : Set X)}
  have hlower : IsClosed lower :=
    hL.preimage (continuous_snd.comp continuous_subtype_val)
  have hfixed : IsClosed fixed := by
    change IsClosed ({p : E | p.val.1 = 0} ∪ {p : E | p.val.2 ∈ (B : Set X)})
    exact (isClosed_singleton.preimage (continuous_fst.comp continuous_subtype_val)).union
      (B.closed.preimage (continuous_snd.comp continuous_subtype_val))
  have hcover (p : E) : p ∈ lower ∨ p ∈ fixed := by
    rcases p.property with hbottom | hlower | hside
    · exact Or.inr (Or.inl hbottom)
    · exact Or.inl hlower
    · exact Or.inr (Or.inr hside)
  let lowerMap : C(lower, unitInterval × L) :=
    ⟨fun p ↦ (p.val.val.1, ⟨p.val.val.2, p.property⟩), by
      have hraw : Continuous (fun p : lower ↦ p.val.val) :=
        continuous_subtype_val.comp continuous_subtype_val
      exact (continuous_fst.comp hraw).prodMk
        ((continuous_snd.comp hraw).subtype_mk _)⟩
  let f : C(lower, C₀) := R.comp lowerMap
  let g : C(fixed, C₀) :=
    ⟨fun p ↦ ⟨p.val.val, p.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  have hagree (p : E) (hpL : p ∈ lower) (hpF : p ∈ fixed) :
      f ⟨p, hpL⟩ = g ⟨p, hpF⟩ := by
    apply Subtype.ext
    change (R (p.val.1, ⟨p.val.2, hpL⟩)).val = (p.val.1, p.val.2)
    rcases hpF with hbottom | hside
    · rw [hbottom]
      exact hRbottom ⟨p.val.2, hpL⟩
    · exact hRside p.val.1 ⟨p.val.2, hpL⟩ hside
  obtain ⟨K, hKlower, hKfixed⟩ := cw_glue_two_closed lower fixed hlower hfixed hcover f g hagree
  refine ⟨K, ?_, ?_⟩
  · intro t x
    exact hKlower ⟨(t, x.val), Or.inr (Or.inl x.property)⟩ x.property
  · intro p
    exact congrArg Subtype.val (hKfixed
      ⟨p.val, p.property.elim Or.inl (fun hb ↦ Or.inr (Or.inr hb))⟩ p.property)

end HolomorphicAnosov
