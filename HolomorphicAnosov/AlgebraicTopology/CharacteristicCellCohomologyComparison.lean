import HolomorphicAnosov.AlgebraicTopology.SingularCohomologyProductDeformationRetraction
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SourceCollarDeformationLaws
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SourceCollarDeformation
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SourceBoundaryRetraction
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SourceInnerBallExcision
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollarStrongDeformationRetraction
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.IsOpenSkeletonCollar
import Mathlib.Topology.CompactOpen
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SourceCollarCohomology
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollarCohomology
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.InnerBallGeometry
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.InnerBallRelativePullback
import HolomorphicAnosov.AlgebraicTopology.SingularRelativePullbackRestrictionSquare
import HolomorphicAnosov.AlgebraicTopology.SingularRelativeCohomologyComparison
import HolomorphicAnosov.AlgebraicTopology.SingularRelativeCohomologyExcision
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCellMapsTo
import HolomorphicAnosov.AlgebraicTopology.SingularRelativeCohomologyPairTheorems
import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.LinearAlgebra.Pi
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCellComparison.SigmaProductInnerBallTransport
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCellComparison.CharacteristicProductAssembly

/-!
# Characteristic-cell relative cohomology comparison

Source: Hatcher, Algebraic Topology, Proposition3.17 p.217, pp.201--202,
Proposition2.22 p.124, AppendixA.2 p.521 and A.17 pp.532--533.
The groups are the shared actual relative singular-cochain kernel/image quotients.
Pair pullbacks are the shared kernel maps of the genuine restriction square.
The native CW characteristic maps use closed maximum-norm balls, homeomorphic
standard disks, and their sphere boundaries. ULift only aligns type universes.
No orientation choice or injectivity on attaching boundaries is imposed.
-/

open CategoryTheory CategoryTheory.Limits Opposite Set _root_.Topology

universe u

noncomputable section


namespace HolomorphicAnosov.CharacteristicCellComparison

open SingularCochain

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000


variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]


/-- Hatcher p.217: component pullbacks, the canonical characteristic pullback followed by restrictions. -/
def characteristicPullback (R : Type u) [CommRing R] (m k : ℕ) :
    relativeCohomology R (TopCat.of (Skeleton X m)) (lowerSkeleton X m) k →ₗ[R]
      (∀ _i : RelCWComplex.cell (univ : Set X) m,
        relativeCohomology R (TopCat.of (CellDisk.{u} m)) (cellBoundary m) k) :=
  LinearMap.pi fun i ↦
    (relativeCohomologyPullback R (TopCat.ofHom (characteristicCell X m i))
      (characteristicCell_mapsTo X m i) k).hom

/-- Hatcher p.217: the ordinary product characteristic map, with the original topology on Y. -/
def characteristicCellProd (Y : Type u) [TopologicalSpace Y]
    (m : ℕ) (i : RelCWComplex.cell (univ : Set X) m) :
    C(CellDisk.{u} m × Y, Skeleton X m × Y) :=
  (characteristicCell X m i).prodMap (ContinuousMap.id Y)

/-- Hatcher p.217: the boundary-times-Y subspace in the ordinary product. -/
def boundaryProduct (Y : Type u) (m : ℕ) : Set (CellDisk.{u} m × Y) :=
  {z | z.1 ∈ cellBoundary m}

/-- Hatcher p.217: the preceding-skeleton-times-Y subspace in the ordinary product. -/
def lowerSkeletonProduct (Y : Type u) (m : ℕ) : Set (Skeleton X m × Y) :=
  {z | z.1 ∈ lowerSkeleton X m}

/-- Hatcher p.217: product characteristic boundaries land in the actual product subspace. -/
theorem characteristicCellProd_mapsTo (Y : Type u) [TopologicalSpace Y]
    (m : ℕ) (i : RelCWComplex.cell (univ : Set X) m) :
    MapsTo (characteristicCellProd X Y m i) (boundaryProduct Y m)
      (lowerSkeletonProduct X Y m) := by
  intro z hz
  exact characteristicCell_mapsTo X m i hz

/-- Hatcher p.217: the actual product characteristic pullback with disjoint-union restrictions. -/
def characteristicProductPullback (R : Type u) [CommRing R]
    (Y : Type u) [TopologicalSpace Y] (m k : ℕ) :
    relativeCohomology R (TopCat.of (Skeleton X m × Y)) (lowerSkeletonProduct X Y m) k →ₗ[R]
      (∀ _i : RelCWComplex.cell (univ : Set X) m,
        relativeCohomology R (TopCat.of (CellDisk.{u} m × Y)) (boundaryProduct Y m) k) :=
  LinearMap.pi fun i ↦
    (relativeCohomologyPullback R (TopCat.ofHom (characteristicCellProd X Y m i))
      (characteristicCellProd_mapsTo X Y m i) k).hom

/--
Source: Hatcher, Algebraic Topology, Proposition3.17 printed p.217, characteristic-map excision
reduction; relative excision pp.201–202 and good-pair neighborhood comparison Proposition2.22 p.124.
Finite attaching topology: Appendix PropositionA.2 p.521 (written converse attaching-quotient
proof); product descent: Appendix PropositionA.17 pp.532–533; acquired literature/hatcher-at.pdf and
.txt. The collar argument below expands the source excision step.

Complete natural-language proof of topo.finite_cw_characteristic_cell_cohomology_comparison_g2:

1. For m=0 the characteristic map is a homeomorphism from the finite discrete union of points onto
X^0, and all attaching boundaries are empty, so both assertions follow directly from finite
disjoint-union splitting. For m≥1 write Z=X^m and A=X^(m−1). The finite characteristic attachment
presents Z as the quotient of A⊔⊔D^m_α with only boundary points identified through their attaching
maps. This follows from the finite closed-cell closed-set criterion: a subset of Z is closed exactly
when its pullback to A and each closed cell disk is closed. Thus the quotient description uses the
given CW topology, not a replacement topology. On each open disk the map is a homeomorphism onto its
open m-cell in Z.

2. Let U contain A and the images of every cell point with radial coordinate r>1/2. In the
attachment quotient its full preimage is A plus the open collars r>1/2, so U is open in Z. Let V be
the disjoint union of the cell interiors r<3/4; it is open in Z and U∪V=Z. The intersection U∩V is
the disjoint union of 1/2<r<3/4 annuli. The radial formula r↦(1−t)r+t, keeping direction fixed,
strongly deformation retracts U onto A; at r=1 its value is the same attaching point for all t, so
it agrees with the identity on A even if attaching maps identify many boundary points. Joint
continuity follows from quotient descent with locally compact I; restricting the attachment quotient
to the open preimage of U remains a quotient. After taking the ordinary product with Y this same
homotopy times id_Y strongly deformation retracts U×Y onto A×Y. Only the I quotient-descent theorem
is needed for the homotopy; no assumption that product CW topology equals some finer topology is
made.

3. On the disjoint union of disks let U0 be the outer collars r>1/2 and V0 the inner balls r<3/4,
with boundary union S. The radial formula strongly retracts U0 onto S. The original characteristic
map is a map of pairs (disk union,S)→(Z,A), and also of enlarged pairs (disk union,U0)→(Z,U).
Homotopy invariance gives cohomology isomorphisms of U→A and U0→S. Compare long exact sequences for
the identity on the two ambient spaces and these inclusions; the five lemma gives isomorphisms for
the relative maps replacing A by U and S by U0. The same comparison holds after product with Y
because the homotopies are jointly continuous in the ordinary product topology.

4. Apply relative excision to the open cover U,V of Z and to U0,V0 of the disk union, also after
product with Y, where the cover is U×Y,V×Y. The restricted characteristic map V0→V is a
homeomorphism, carrying U0∩V0 exactly onto U∩V, since only boundary points are identified in the
characteristic quotient and these inner balls miss the boundaries. Its ordinary product with id_Y is
also a homeomorphism. Consequently the enlarged-pair excision square has three isomorphisms, so its
fourth canonical characteristic pullback is an isomorphism. Combining with the preceding pair
comparisons proves the original Φ* and (Φ×id_Y)* assertions. The finite disjoint-union restriction
theorem identifies the disk-union groups with the displayed products. All squares use the actual
pair maps, so no unspecified relative isomorphism replaces the characteristic pullback.

5. If there are no m-cells, X^m=X^(m−1), both left relative groups are zero, and the empty right
product is the zero module. For m=1 the sphere boundary is two points; the same radial collar
formulas work on the two open intervals and identify their attaching endpoints without any
distinct-vertex assumption. Empty Y makes every product space empty and the product assertion
trivial. These checks use ordinary relative H^0 as well as higher degrees; there is no
reduced-theory basepoint convention.

-/
theorem finite_cw_characteristic_cell_cohomology_comparison
    (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
    [CWComplex.Finite (univ : Set X)] (R : Type u) [CommRing R]
    (Y : Type u) [TopologicalSpace Y] [T2Space Y] [CWComplex (univ : Set Y)]
    [CWComplex.Finite (univ : Set Y)] (m k : ℕ) :
    Function.Bijective (characteristicPullback X R m k) ∧
      Function.Bijective (characteristicProductPullback X R Y m k) := by
  classical
  let : Finite (RelCWComplex.cell (univ : Set X) m) :=
    RelCWComplex.FiniteType.finite_cell m
  let := Fintype.ofFinite (RelCWComplex.cell (univ : Set X) m)
  -- Functoriality here only identifies the concrete component maps.
  have hcomp {P Q T : TopCat.{u}} {A : Set P} {B : Set Q} {C : Set T}
      (f : P ⟶ Q) (g : Q ⟶ T) (hf : MapsTo f A B) (hg : MapsTo g B C) :
      relativeCohomologyPullback R (f ≫ g) (hg.comp hf) k =
        relativeCohomologyPullback R g hg k ≫ relativeCohomologyPullback R f hf k := by
    have hc : relativePullback R (f ≫ g) (hg.comp hf) =
        relativePullback R g hg ≫ relativePullback R f hf := by
      apply (cancel_mono (kernel.ι (pullback R (subspaceInclusion P A)))).mp
      dsimp only [relativePullback, kernel.map]
      simp only [Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc]
      change kernel.ι (pullback R (subspaceInclusion T C)) ≫
          (cochainFunctor R).map (f ≫ g).op =
        kernel.ι (pullback R (subspaceInclusion T C)) ≫
          (cochainFunctor R).map g.op ≫ (cochainFunctor R).map f.op
      simp only [op_comp, Functor.map_comp]
    dsimp only [relativeCohomologyPullback]
    rw [hc]
    dsimp only [quotientMap]
    rw [HomologicalComplex.homologyMap_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  -- Hatcher's finite-disjoint-union reduction preserves the actual pullback.
  have hsplit (P : RelCWComplex.cell (univ : Set X) m → TopCat.{u})
      (A : ∀ i, Set (P i)) (Z : TopCat.{u}) (B : Set Z)
      (f : ∀ i, P i ⟶ Z) (hf : ∀ i, MapsTo (f i) (A i) B) :
      let Φ : sumSpace P ⟶ Z := TopCat.ofHom
        ⟨fun z ↦ f z.1 z.2, continuous_sigma fun i ↦ (f i).hom.continuous⟩
      Function.Bijective (relativeCohomologyPullback R Φ
        (fun z hz ↦ hf z.1 hz) k) →
      Function.Bijective (LinearMap.pi fun i ↦
        (relativeCohomologyPullback R (f i) (hf i) k).hom) := by
    intro Φ hΦ
    have hs := (relative_cohomology_pair_theorems R).2.2.2.1
      (RelCWComplex.cell (univ : Set X) m) P A k
    have heq : (sumRestriction R P A k).comp
        (relativeCohomologyPullback R Φ (fun z hz ↦ hf z.1 hz) k).hom =
        LinearMap.pi (fun i ↦ (relativeCohomologyPullback R (f i) (hf i) k).hom) := by
      ext c i
      have hc := congrArg (fun t ↦ t c)
        (hcomp (A := A i) (B := sumSubspace P A)
          (summandInclusion P i) Φ (fun _ hz ↦ hz) (fun z hz ↦ hf z.1 hz))
      exact hc.symm
    rw [← heq]
    exact hs.comp hΦ
  let D : TopCat.{u} := TopCat.of
    (Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m)
  let S : Set D := {z | z.2 ∈ cellBoundary m}
  let Φ : D ⟶ TopCat.of (Skeleton X m) := TopCat.ofHom
    ⟨fun z ↦ characteristicCell X m z.1 z.2,
      continuous_sigma fun i ↦ (characteristicCell X m i).continuous⟩
  have hΦ : MapsTo Φ S (lowerSkeleton X m) :=
    fun z hz ↦ characteristicCell_mapsTo X m z.1 hz
  let DY : TopCat.{u} := TopCat.of
    (Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m × Y)
  let SY : Set DY := {z | z.2 ∈ boundaryProduct Y m}
  let ΦY : DY ⟶ TopCat.of (Skeleton X m × Y) := TopCat.ofHom
    ⟨fun z ↦ characteristicCellProd X Y m z.1 z.2,
      continuous_sigma fun i ↦ (characteristicCellProd X Y m i).continuous⟩
  have hΦY : MapsTo ΦY SY (lowerSkeletonProduct X Y m) :=
    fun z hz ↦ characteristicCellProd_mapsTo X Y m z.1 hz
  suffices hcomparison :
      Function.Bijective (relativeCohomologyPullback R Φ hΦ k) ∧
      Function.Bijective (relativeCohomologyPullback R ΦY hΦY k) by
    constructor
    · exact hsplit (fun _ ↦ TopCat.of (CellDisk.{u} m)) (fun _ ↦ cellBoundary m)
        (TopCat.of (Skeleton X m)) (lowerSkeleton X m)
        (fun i ↦ TopCat.ofHom (characteristicCell X m i))
        (characteristicCell_mapsTo X m) hcomparison.1
    · exact hsplit (fun _ ↦ TopCat.of (CellDisk.{u} m × Y))
        (fun _ ↦ boundaryProduct Y m) (TopCat.of (Skeleton X m × Y))
        (lowerSkeletonProduct X Y m)
        (fun i ↦ TopCat.ofHom (characteristicCellProd X Y m i))
        (characteristicCellProd_mapsTo X Y m) hcomparison.2
  constructor
  · let U0 : Set D := {z | (1 / 2 : ℝ) < ‖z.2.down.1‖}
    let V0 : Set D := {z | ‖z.2.down.1‖ < (3 / 4 : ℝ)}
    let U : Set (Skeleton X m) := skeletonCollar X m
    let V : Set (Skeleton X m) := innerBallImage X m
    have hU0 : IsOpen U0 := by
      rw [isOpen_sigma_iff]
      intro i
      exact isOpen_lt continuous_const ((continuous_subtype_val.comp continuous_uliftDown).norm)
    have hV0 : IsOpen V0 := by
      rw [isOpen_sigma_iff]
      intro i
      exact isOpen_lt ((continuous_subtype_val.comp continuous_uliftDown).norm) continuous_const
    have hcover0 : interior U0 ∪ interior V0 = univ := by
      rw [hU0.interior_eq, hV0.interior_eq]
      apply Set.eq_univ_of_forall
      intro z
      by_cases hz : (1 / 2 : ℝ) < ‖z.2.down.1‖
      · exact Or.inl hz
      · exact Or.inr (by dsimp [V0]; linarith)
    have hgeom := innerBallImage_geometry X m
    have hcover : interior U ∪ interior V = univ := by
      rw [(isOpen_skeletonCollar X m).interior_eq, hgeom.2.2.1.interior_eq]
      exact hgeom.2.2.2
    have hΦU : MapsTo Φ U0 U := by
      intro z hz
      exact Or.inr ⟨⟨z.1, ⟨z.2, hz⟩⟩, rfl⟩
    have hΦV : MapsTo Φ V0 V := fun z hz ↦ ⟨z.1, z.2, hz, rfl⟩
    let r0 := relativeCohomologyPullback R (X := TopCat.of V0) (Y := D)
      (A := {z | z.1 ∈ U0}) (B := U0) (subspaceInclusion D V0) (fun _ hz ↦ hz) k
    let rZ := relativeCohomologyPullback R (X := TopCat.of V)
      (Y := TopCat.of (Skeleton X m)) (A := {z | z.1 ∈ U}) (B := U)
      (subspaceInclusion (TopCat.of (Skeleton X m)) V) (fun _ hz ↦ hz) k
    let inner := relativeCohomologyPullback R (X := TopCat.of V0) (Y := TopCat.of V)
      (A := {z | z.1 ∈ U0}) (B := {z | z.1 ∈ U})
      (pairSubspaceMap Φ hΦV) (fun _ hz ↦ hΦU hz) k
    have : IsIso r0 := relative_cohomology_excision R D U0 V0 hcover0 k
    have : IsIso rZ := relative_cohomology_excision R (TopCat.of (Skeleton X m)) U V hcover k
    have : IsIso inner := by
      obtain ⟨hp, hi, _⟩ := innerBallCharacteristic_relative_pullback_isIso X R m k
      exact hi
    let large := relativeCohomologyPullback R Φ hΦU k
    have hsquare : large ≫ r0 = rZ ≫ inner :=
      relativeCohomologyPullback_restriction_square R (X := D)
        (Y := TopCat.of (Skeleton X m)) U0 V0 U V Φ hΦU hΦV k
    have : IsIso (large ≫ r0) := by rw [hsquare]; infer_instance
    have : IsIso large := IsIso.of_isIso_comp_right large r0
    have hSU : S ⊆ U0 := by
      intro z hz
      have hn : ‖z.2.down.1‖ = 1 := by
        simpa only [S, cellBoundary, Set.mem_ofPred_eq, Metric.mem_sphere,
          dist_zero_right] using hz
      change (1 / 2 : ℝ) < ‖z.2.down.1‖
      rw [hn]
      norm_num
    have hAU : lowerSkeleton X m ⊆ U := fun _ hx ↦ Or.inl hx
    have hid (Z : TopCat.{u}) (n : ℕ) :
        Function.Bijective (cohomologyPullback R (𝟙 Z) n) := by
      have he : cohomologyPullback R (𝟙 Z) n = 𝟙 _ := by
        have hp : SingularCochain.pullback R (𝟙 Z) = 𝟙 _ :=
          (cochainFunctor R).map_id (op Z)
        unfold cohomologyPullback
        rw [hp]
        unfold quotientMap
        rw [HomologicalComplex.homologyMap_id]
        let e := (HomologicalComplex.sc (complex R Z) n).moduleCatHomologyIso
        change e.inv ≫ 𝟙 _ ≫ e.hom = 𝟙 _
        simp only [Category.id_comp, Iso.inv_hom_id]
      rw [he]
      exact Function.bijective_id
    let iD := relativeCohomologyPullback R (X := D) (Y := D)
      (A := S) (B := U0) (𝟙 D) hSU k
    let iZ := relativeCohomologyPullback R (X := TopCat.of (Skeleton X m))
      (Y := TopCat.of (Skeleton X m)) (A := lowerSkeleton X m) (B := U)
      (𝟙 _) hAU k
    have : IsIso iD := (ConcreteCategory.isIso_iff_bijective iD).mpr
      (relative_cohomology_pullback_bijective_of_absolute R (𝟙 D) hSU (hid D)
        (fun n ↦ (ConcreteCategory.isIso_iff_bijective _).mp
          (sourceCollar_cohomology_isIso X R m n hSU)) k)
    have : IsIso iZ := (ConcreteCategory.isIso_iff_bijective iZ).mpr
      (relative_cohomology_pullback_bijective_of_absolute R
        (X := TopCat.of (Skeleton X m)) (Y := TopCat.of (Skeleton X m))
        (A := lowerSkeleton X m) (B := U) (𝟙 _) hAU
        (hid (TopCat.of (Skeleton X m)))
        (fun n ↦ (ConcreteCategory.isIso_iff_bijective _).mp
          (skeletonCollar_cohomology_isIso X R m n hAU)) k)
    have hcollars : large ≫ iD = iZ ≫ relativeCohomologyPullback R Φ hΦ k := by
      dsimp only [large, iD, iZ]
      rw [← hcomp, ← hcomp]
      congr 1
    have : IsIso (iZ ≫ relativeCohomologyPullback R Φ hΦ k) := by
      rw [← hcollars]
      infer_instance
    have : IsIso (relativeCohomologyPullback R Φ hΦ k) :=
      IsIso.of_isIso_comp_left iZ _
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  · -- The ordinary product preserves both explicit collar deformations.
    let U0 : Set D := {z | (1 / 2 : ℝ) < ‖z.2.down.1‖}
    let V0 : Set D := {z | ‖z.2.down.1‖ < (3 / 4 : ℝ)}
    let U : Set (Skeleton X m) := skeletonCollar X m
    let V : Set (Skeleton X m) := innerBallImage X m
    let U0Y : Set DY := {z | (1 / 2 : ℝ) < ‖z.2.1.down.1‖}
    let V0Y : Set DY := {z | ‖z.2.1.down.1‖ < (3 / 4 : ℝ)}
    let UY : Set (Skeleton X m × Y) := {z | z.1 ∈ U}
    let VY : Set (Skeleton X m × Y) := {z | z.1 ∈ V}
    have hU0 : IsOpen U0 := by
      rw [isOpen_sigma_iff]
      intro i
      exact isOpen_lt continuous_const ((continuous_subtype_val.comp continuous_uliftDown).norm)
    have hV0 : IsOpen V0 := by
      rw [isOpen_sigma_iff]
      intro i
      exact isOpen_lt ((continuous_subtype_val.comp continuous_uliftDown).norm) continuous_const
    have hU0Y : IsOpen U0Y := by
      rw [isOpen_sigma_iff]
      intro i
      change IsOpen {p : CellDisk.{u} m × Y | (1 / 2 : ℝ) < ‖p.1.down.1‖}
      exact (isOpen_lt continuous_const
        ((continuous_subtype_val.comp continuous_uliftDown).norm)).preimage continuous_fst
    have hV0Y : IsOpen V0Y := by
      rw [isOpen_sigma_iff]
      intro i
      change IsOpen {p : CellDisk.{u} m × Y | ‖p.1.down.1‖ < (3 / 4 : ℝ)}
      exact (isOpen_lt
        ((continuous_subtype_val.comp continuous_uliftDown).norm)
        continuous_const).preimage continuous_fst
    have hU : IsOpen U := isOpen_skeletonCollar X m
    have hV : IsOpen V := innerBallImage_geometry X m |>.2.2.1
    have hUY : IsOpen UY := hU.preimage continuous_fst
    have hVY : IsOpen VY := hV.preimage continuous_fst
    have hΦU : MapsTo Φ U0 U := by
      intro z hz
      exact Or.inr ⟨⟨z.1, ⟨z.2, hz⟩⟩, rfl⟩
    have hΦV : MapsTo Φ V0 V := fun z hz ↦ ⟨z.1, z.2, hz, rfl⟩
    have hcover0Y : interior U0Y ∪ interior V0Y = (Set.univ : Set DY) := by
      rw [hU0Y.interior_eq, hV0Y.interior_eq]
      apply Set.eq_univ_of_forall
      intro z
      by_cases hz : (1 / 2 : ℝ) < ‖z.2.1.down.1‖
      · exact Or.inl hz
      · exact Or.inr (by dsimp [V0Y]; linarith)
    have hcoverY : interior UY ∪ interior VY = (Set.univ : Set (Skeleton X m × Y)) := by
      rw [hUY.interior_eq, hVY.interior_eq]
      apply Set.eq_univ_of_forall
      intro z
      have hz := Set.mem_univ z.1
      rw [← (innerBallImage_geometry X m).2.2.2] at hz
      exact hz
    have hΦYU : MapsTo ΦY U0Y UY := by
      intro z hz
      have hz0 : (⟨z.1, z.2.1⟩ : D) ∈ U0 := by
        change (1 / 2 : ℝ) < ‖z.2.1.down.1‖
        exact hz
      have hzU := hΦU hz0
      change (characteristicCell X m z.1 z.2.1) ∈ U
      exact hzU
    have hΦYV : MapsTo ΦY V0Y VY := by
      intro z hz
      have hz0 : (⟨z.1, z.2.1⟩ : D) ∈ V0 := by
        change ‖z.2.1.down.1‖ < (3 / 4 : ℝ)
        exact hz
      have hzV := hΦV hz0
      change (characteristicCell X m z.1 z.2.1) ∈ V
      exact hzV
    let r0Y := relativeCohomologyPullback R (X := TopCat.of V0Y) (Y := DY)
      (A := {z | z.1 ∈ U0Y}) (B := U0Y) (subspaceInclusion DY V0Y) (fun _ hz ↦ hz) k
    let rZY := relativeCohomologyPullback R (X := TopCat.of VY)
      (Y := TopCat.of (Skeleton X m × Y)) (A := {z | z.1 ∈ UY}) (B := UY)
      (subspaceInclusion (TopCat.of (Skeleton X m × Y)) VY) (fun _ hz ↦ hz) k
    let innerY := relativeCohomologyPullback R (X := TopCat.of V0Y) (Y := TopCat.of VY)
      (A := {z | z.1 ∈ U0Y}) (B := {z | z.1 ∈ UY})
      (pairSubspaceMap ΦY hΦYV) (fun _ hz ↦ hΦYU hz) k
    have : IsIso r0Y := relative_cohomology_excision R DY U0Y V0Y hcover0Y k
    have : IsIso rZY := relative_cohomology_excision R (TopCat.of (Skeleton X m × Y))
      UY VY hcoverY k
    let ψ : DY ⟶ TopCat.of (Skeleton X m × Y) := TopCat.ofHom
      ⟨fun z ↦ (characteristicCell X m z.1 z.2.1, z.2.2),
        continuous_sigma fun i ↦
          ((characteristicCell X m i).continuous.comp continuous_fst).prodMk continuous_snd⟩
    have hψ : ΦY = ψ := by
      ext z : 1
      rfl
    have : IsIso innerY := by
      simpa only [innerY, hψ] using
        (sigmaProduct_innerBall_pairSubspace_isIso X R Y m k)
    let largeY := relativeCohomologyPullback R ΦY hΦYU k
    have hsquareY : largeY ≫ r0Y = rZY ≫ innerY :=
      relativeCohomologyPullback_restriction_square R (X := DY)
        (Y := TopCat.of (Skeleton X m × Y)) U0Y V0Y UY VY ΦY hΦYU hΦYV k
    have : IsIso (largeY ≫ r0Y) := by rw [hsquareY]; infer_instance
    have : IsIso largeY := IsIso.of_isIso_comp_right largeY r0Y
    have hSU : S ⊆ U0 := by
      intro z hz
      have hn : ‖z.2.down.1‖ = 1 := by
        simpa only [S, cellBoundary, Set.mem_ofPred_eq, Metric.mem_sphere,
          dist_zero_right] using hz
      change (1 / 2 : ℝ) < ‖z.2.down.1‖
      rw [hn]
      norm_num
    have hsource (n : ℕ) : IsIso (cohomologyPullback R
        (TopCat.ofHom ((ContinuousMap.inclusion hSU).prodMap
          (ContinuousMap.id Y))) n) := by
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
      exact cohomologyPullback_prod_isIso_of_deformationRetraction R
        (TopCat.ofHom i) (TopCat.ofHom r) hr H Y n
    have hAU : lowerSkeleton X m ⊆ skeletonCollar X m := fun _ hx ↦ Or.inl hx
    have htarget (n : ℕ) : IsIso (cohomologyPullback R
        (TopCat.ofHom ((ContinuousMap.inclusion hAU).prodMap
          (ContinuousMap.id Y))) n) := by
      obtain ⟨hAU', r, hr, ⟨H⟩⟩ := skeletonCollar_strongDeformationRetraction X m
      apply cohomologyPullback_prod_isIso_of_deformationRetraction R
        (TopCat.ofHom (ContinuousMap.inclusion hAU)) (TopCat.ofHom r) _
        (show TopCat.Homotopy (𝟙 (TopCat.of ↥(skeletonCollar X m)))
          (TopCat.ofHom r ≫ TopCat.ofHom (ContinuousMap.inclusion hAU))
          from H.toHomotopy) Y n
      ext a : 1
      exact hr a
    exact (characteristic_product_relative_pullback_core X R Y m k)

end HolomorphicAnosov.CharacteristicCellComparison
