import HolomorphicAnosov.Topology.BoundaryConeRadialG9
import Mathlib.Topology.Maps.Strict.Basic
import HolomorphicAnosov.Topology.GallierXuCarrierCompact
import HolomorphicAnosov.Topology.HalfSectorSegmentCompactConnected

/-!
# Compact boundary cycles and closed radial caps

Gallier--Xu Chapter 2, geometric realizations: a finite cycle is a finite union
of closed edges in the compact finite carrier. Its radial cone image is compact
as the continuous image of its product with the closed unit interval. This
supplies the closed-cap side of the capping argument for Theorems 5.1--5.2.
-/
open Set
open scoped Classical
namespace HolomorphicAnosov.Topology.GallierXu

/-- The boundary-cycle contour is closed in the finite carrier, even without
simplicity or edge-face hypotheses. It is a finite union of closed segments
restricted to that carrier. -/
theorem cycleCarrier_isClosed_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N)) :
    IsClosed (cycleCarrier (K := K) l) := by
  have heq : cycleCarrier (K := K) l =
      ⋃ u : Fin N, ⋃ v : Fin N,
        if cycleEdge l u v then
          (Subtype.val : ↥(carrier K) → (Fin N → ℝ)) ⁻¹'
            segment ℝ (Pi.single u 1) (Pi.single v 1) else ∅ := by
    ext x
    simp only [cycleCarrier, Set.mem_ofPred_eq, Set.mem_iUnion]
    apply exists_congr
    intro u
    apply exists_congr
    intro v
    split_ifs <;> simp_all
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro u
  apply isClosed_iUnion_of_finite
  intro v
  split_ifs
  · exact (HolomorphicAnosov.halfSector_segment_compact_connected _ _).1.isClosed.preimage
      continuous_subtype_val
  · exact isClosed_empty

/-- Finite barycentric cycle contours are compact. -/
theorem cycleCarrier_isCompact_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N)) :
    IsCompact (cycleCarrier (K := K) l) := by
  have : CompactSpace ↥(carrier K) := isCompact_iff_compactSpace.mp (triangle_carrier_compact K)
  exact (cycleCarrier_isClosed_g9 K l).isCompact

/-- The actual radial cap image is compact, hence closed in the attached carrier.
Together with coverage and the closed zero-height inclusion, this verifies the
closed-cover hypotheses required for boundary-respecting chart pasting. -/
theorem boundaryConeRadialMap_compact_closed_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N)) :
    IsCompact (range (boundaryConeRadialMap K l)) ∧
    IsClosed (range (boundaryConeRadialMap K l)) := by
  have : CompactSpace ↥(cycleCarrier (K := K) l) :=
    isCompact_iff_compactSpace.mp (cycleCarrier_isCompact_g9 K l)
  have hc := isCompact_range (boundaryConeRadialMap K l).continuous
  exact ⟨hc, hc.isClosed⟩

/-- The radial map induces the quotient topology on its image. -/
theorem boundaryConeRadialMap_isStrictMap_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N)) :
    _root_.Topology.IsStrictMap (boundaryConeRadialMap K l) := by
  have : CompactSpace ↥(cycleCarrier (K := K) l) :=
    isCompact_iff_compactSpace.mp (cycleCarrier_isCompact_g9 K l)
  exact (boundaryConeRadialMap K l).continuous.isClosedMap.isStrictMap
    (boundaryConeRadialMap K l).continuous

/-- The abstract cone quotient is homeomorphic to the actual radial cap.
The kernel relation is exactly equal heights with either equal base points or
height one, by `boundaryConeRadialMap_eq_iff_g9`. Thus this is the boundary
cylinder with only its upper rim collapsed, not an assumed disk identification.
Source: Gallier--Xu Chapter 2 geometric realization and the compact quotient
criterion; explicit coordinate realization of the cone construction. -/
noncomputable def boundaryConeRadialQuotientHomeomorph_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N)) :
    Quotient (Setoid.ker (boundaryConeRadialMap K l)) ≃ₜ
      ↥(range (boundaryConeRadialMap K l)) :=
  Homeomorph.quotientKerEquivRange (boundaryConeRadialMap_isStrictMap_g9 K l)

end HolomorphicAnosov.Topology.GallierXu

