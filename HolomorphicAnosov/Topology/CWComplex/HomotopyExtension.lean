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
import HolomorphicAnosov.Topology.CWComplex.PairCylinderRetraction

/-!
# Homotopy extension for arbitrary Hausdorff CW pairs

Source: Hatcher, *Algebraic Topology*, Chapter 0, Proposition 0.16, pp.14–15;
Appendix A.2, pp.520–521, and A.17, pp.532–533. The characteristic-disk change
from Euclidean balls to Mathlib's finite maximum-norm balls is the radial
ball/cube homeomorphism of Bredon, *Topology and Geometry*, I.16, pp.56–57.
All spaces and subcomplexes below are Mathlib's existing structures.
-/

namespace HolomorphicAnosov

universe u v


/-- A homotopy on a subcomplex of a Hausdorff CW complex extends over the whole
complex, with its given initial map. Any smaller subcomplex fixed by the given
homotopy is fixed by this same extension.

Source and complete natural-language proof: Hatcher, Proposition 0.16,
pp.14–15, with the weak-topology and product-quotient results of Appendix A.2
and A.17. Write X_m for the original skeleta and B_m = B ∩ X_m, and put
C = X×{0} ∪ B×I. Subcomplexes and skeleta are closed. The disjoint union of
the closed characteristic disks maps onto X by a quotient map: each disk maps
onto its closed cell by a compact-to-Hausdorff quotient map, and the CW weak
closed-set criterion gives the quotient criterion on the union. The same
argument applies to each skeleton. Taking products with the compact interval
preserves these quotient maps; apply this twice when a deformation parameter
is also present.

Hatcher's radial projection from (0,2) has the same formula on the closed
unit ball of any real normed space: put a = max(‖x‖,(2−u)/2) and
r(x,u) = (a⁻¹ • x, 2+(u−2)/a). The proof uses this formula directly on
Mathlib's characteristic maximum-norm balls. Here 1/2≤a≤1 and ‖x‖≤a,
so r stays in the prism; its height lies between 0 and u. If
a=(2−u)/2 its height is zero, and if a=‖x‖ its disk coordinate has norm
one. On the bottom or sphere a=1, so r fixes these sets pointwise.
The interpolation (1−s)z+s r(z) stays in the convex prism, is continuous
because a is positive, starts at the identity, and fixes the bottom and
sphere throughout. For n=0 it is (0,u) ↦ (0,(1−s)u).

For each n, use this deformation on the n-cells outside B, and the identity
on B_n and X_(n−1). Distinct open cells are disjoint and each characteristic
map is injective on its open ball. An active-cell representative whose
image lies in B or X_(n−1) must lie on the sphere: its open cell is disjoint
from that subcomplex. Thus all mixed prescriptions agree, and sphere
fixedness also handles every boundary identification, without requiring
boundary injectivity. The product quotient gives a continuous stage on
X_n×I, starting at the identity, fixing X_n×{0} ∪ (X_(n−1)∪B_n)×I,
and mapping into this set at its endpoint, since characteristic spheres
lie in the lower skeleton.

For the HEP conclusion, retain the compatible endpoints of Hatcher's
skeletal construction. Begin with the unique map on X_(-1)×I=∅. Given a
continuous R_(n−1):X_(n−1)×I→C fixing its bottom and B cylinder, extend it
by the identity on C to K_n:C ∪ (X_(n−1)×I)→C. These are closed pieces
and the maps agree on their intersection by the assumed fixedness, so
closed pasting proves continuity. Compose K_n with the selected n-stage
endpoint to obtain R_n:X_n×I→C. This fixes the bottom and B_n×I, and its
restriction to X_(n−1)×I equals R_(n−1), because that stage fixes the lower
skeleton. Natural-number recursion chooses these successive extensions;
induction gives compatibility for every pair of nested skeleta.

Every point of X belongs to a finite skeleton, so the compatible R_n
define r_X:X×I→C. On each characteristic d-disk times I this map agrees
with the continuous R_d pulled back along the characteristic map. The
weak-topology and locally compact product-quotient criterion of Appendix
A.2 and A.17 therefore proves continuity for the ordinary product topology.
Bottom and B fixedness pass from the finite stages to r_X. Every c∈C is
its own preimage, so r_X is a retraction onto C. This implements the endpoint
needed from Proposition 0.16 without constructing the entire dyadic
deformation parameter.

The maps f on X×{0} and h, with the factors exchanged, on B×I agree on
B×{0} by the hypothesis. Both pieces are closed, so they paste to a
continuous map k:C→Y; Y need not be Hausdorff. Compose k with the retraction
and exchange factors to obtain H:I×X→Y. The retraction fixes C, giving
H(0,x)=f(x) and H(t,b)=h(t,b). The latter equality immediately implies the
fixed-subcomplex conclusion for every A≤B. This construction includes empty
X or B, B=X, zero-dimensional cells, and arbitrary numbers and dimensions
of cells, without countability or regularity assumptions.
DAG node: `topo.cw_pair_homotopy_extension`.
-/
theorem cw_pair_homotopy_extension
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    (B : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (f : C(X, Y)) (h : C(unitInterval × (B : Set X), Y))
    (h₀ : ∀ b : (B : Set X), h (0, b) = f b.val) :
    ∃ H : C(unitInterval × X, Y),
      (∀ x : X, H (0, x) = f x) ∧
      (∀ (t : unitInterval) (b : (B : Set X)), H (t, b.val) = h (t, b)) ∧
      ∀ (A : Topology.CWComplex.Subcomplex (Set.univ : Set X)) (hAB : A ≤ B),
        (∀ (t : unitInterval) (a : (A : Set X)),
          h (t, ⟨a.val, hAB a.property⟩) = f a.val) →
        ∀ (t : unitInterval) (a : (A : Set X)), H (t, a.val) = f a.val := by
  let C₀ : Set (unitInterval × X) := {p | p.1 = 0 ∨ p.2 ∈ (B : Set X)}
  obtain ⟨r, hrbottom, hrside, _⟩ := cw_pair_cylinder_retraction B
  let bottom : Set C₀ := {p | p.val.1 = 0}
  let side : Set C₀ := {p | p.val.2 ∈ (B : Set X)}
  have hbottom : IsClosed bottom :=
    isClosed_singleton.preimage (continuous_fst.comp continuous_subtype_val)
  have hside : IsClosed side :=
    B.closed.preimage (continuous_snd.comp continuous_subtype_val)
  let initial : C(bottom, Y) :=
    ⟨fun p ↦ f p.val.val.2,
      f.continuous.comp (continuous_snd.comp
        (continuous_subtype_val.comp continuous_subtype_val))⟩
  let prescribed : C(side, Y) :=
    ⟨fun p ↦ h (p.val.val.1, ⟨p.val.val.2, p.property⟩), by
      have hraw : Continuous (fun p : side ↦ p.val.val) :=
        continuous_subtype_val.comp continuous_subtype_val
      exact h.continuous.comp ((continuous_fst.comp hraw).prodMk
        ((continuous_snd.comp hraw).subtype_mk _))⟩
  have hagree (p : C₀) (hp0 : p ∈ bottom) (hpB : p ∈ side) :
      initial ⟨p, hp0⟩ = prescribed ⟨p, hpB⟩ := by
    change f p.val.2 = h (p.val.1, ⟨p.val.2, hpB⟩)
    rw [show p.val.1 = 0 from hp0]
    exact (h₀ ⟨p.val.2, hpB⟩).symm
  obtain ⟨k, hkbottom, hkside⟩ := cw_glue_two_closed bottom side hbottom hside
    (fun p ↦ p.property) initial prescribed hagree
  refine cw_pair_extension_of_retraction B f h C₀ r k hrbottom hrside ?_ ?_
  · intro x hx
    exact hkbottom ⟨(0, x), hx⟩ rfl
  · intro t b hb
    exact hkside ⟨(t, b.val), hb⟩ b.property

end HolomorphicAnosov
