import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ModTwoContractibleAmbientShift
import HolomorphicAnosov.Topology.Homology.ModTwoAugmentedHomeomorphIso
import HolomorphicAnosov.Topology.Homology.ModTwoContractibleSubspaceComparison
import HolomorphicAnosov.Topology.Homology.ModTwoGoodPairCollapse
import HolomorphicAnosov.Topology.Homology.ModTwoContractibleSubspaceComparison
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundarySphereHomeomorph
import HolomorphicAnosov.Topology.Homology.ModTwoGoodPairCollapse
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundaryCollapseSphereHomeomorph
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundaryCollarRetract
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundary_goodPair_guards
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundary_nonempty
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ReducedHomologyHomeomorphIso

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial ZeroObject
namespace HolomorphicAnosov

/-- The mod-two successor sphere profile is transported through the disk
boundary pair, its good-pair quotient, and the polar disk/sphere homeomorphism.
This is the coefficient-specific Hatcher successor step. -/
theorem modTwoSphereSuccessor (k q : ℕ) :
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    let SU := {x : EuclideanSpace ℝ (Fin (k + 1 + 1)) // ‖x‖ = 1}
    let SL := {x : EuclideanSpace ℝ (Fin (k + 1)) // ‖x‖ = 1}
    let KU := (TopCat.toSSet.obj (TopCat.of SU)).chainComplex R0
    let KL := (TopCat.toSSet.obj (TopCat.of SL)).chainComplex R0
    let εU : KU.X 0 ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
    let εL : KL.X 0 ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
    ∀ (wU : KU.d 1 0 ≫ εU = 0) (wL : KL.d 1 0 ≫ εL = 0),
      Nonempty ((ChainComplex.augment KU εU wU).homology (q + 2) ≅
        (ChainComplex.augment KL εL wL).homology (q + 1)) := by
  dsimp only
  intro wU wL
  let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
  let E : Type := EuclideanSpace ℝ (Fin (k + 1))
  let D := {x : E // ‖x‖ ≤ 1}
  let A : Set D := {x | ‖x.val‖ = 1}
  let V : Set D := {x | (1 : ℝ) / 2 < ‖x.val‖}
  obtain ⟨hclosed, _, hneighborhood⟩ :=
    Topology.Homology.diskBoundary_goodPair_guards (E := E)
  have hA : A.Nonempty := Topology.Homology.diskBoundary_nonempty k
  have hAV : A ⊆ V := by
    intro x hx
    change (1 : ℝ) / 2 < ‖x.val‖
    change ‖x.val‖ = 1 at hx
    rw [hx]
    norm_num
  let : ContractibleSpace (TopCat.of D) := by
    have hc : ContractibleSpace (Metric.closedBall (0 : E) 1) := Metric.contractibleSpace_closedBall (by norm_num)
    have he : Metric.closedBall (0 : E) 1 = Set.ofPred (fun x : E => ‖x‖ ≤ 1) := by
      ext x
      change dist x 0 ≤ 1 ↔ ‖x‖ ≤ 1
      rw [show dist x 0 = ‖x‖ from dist_zero_right x]
    rw [he] at hc
    exact hc
  let : Nonempty A := ⟨hA.choose, hA.choose_spec⟩
  let d : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV :=
    Topology.Homology.diskBoundaryCollarRetract
  let Q := GoodPair.Collapsed A
  let B := GoodPair.collapsedPart A
  let P := singularSubspacePair (TopCat.of D) A
  let PB := singularSubspacePair (TopCat.of Q) B
  let KD := P.right.chainComplex R0
  let εD : KD.X 0 ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
  let KA := P.left.chainComplex R0
  let εA : KA.X 0 ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
  have hwA : KA.d 1 0 ≫ εA = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, SSet.ιChainComplex_d]
    simp [εA, SSet.ιChainComplex, Fin.sum_univ_two]
  have hwd : KD.d 1 0 ≫ εD = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, SSet.ιChainComplex_d]
    simp [εD, SSet.ιChainComplex, Fin.sum_univ_two]
  obtain ⟨hzeroD, hshift⟩ := modTwoContractibleAmbientShift (TopCat.of D) A hwA hwd
  have hcollapse := modTwoGoodPairCollapse (TopCat.of D) A V hA hclosed hAV hneighborhood d (q + 1)
  let : Subsingleton B := ⟨by
    intro x y
    apply Subtype.ext
    obtain ⟨a, ha, hax⟩ := x.property
    obtain ⟨b, hb, hby⟩ := y.property
    rw [← hax, ← hby]
    exact Quotient.sound (Or.inr ⟨ha, hb⟩)⟩
  have hB : B.Nonempty := Set.Nonempty.image (GoodPair.collapse A) hA
  let : Nonempty B := ⟨hB.choose, hB.choose_spec⟩
  let PBK := PB.left.chainComplex R0
  let εB : PBK.X 0 ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
  have hwB : PBK.d 1 0 ≫ εB = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, SSet.ιChainComplex_d]
    simp [εB, SSet.ιChainComplex, Fin.sum_univ_two]
  let PQK := PB.right.chainComplex R0
  let εQ : PQK.X 0 ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
  have hwQ : PQK.d 1 0 ≫ εQ = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, SSet.ιChainComplex_d]
    simp [εQ, SSet.ιChainComplex, Fin.sum_univ_two]
  have hquot := modTwoContractibleSubspaceComparison (TopCat.of Q) B hwB hwQ (q + 1)
  obtain ⟨hshiftq⟩ := hshift q
  have hpol := modTwoAugmentedHomeomorphIso
    (Topology.Homology.diskBoundaryCollapseSphereHomeomorph k)
    hwQ wU (q + 2)
  have hlower := modTwoAugmentedHomeomorphIso
    (Topology.Homology.diskBoundarySphereHomeomorph (E := E))
    hwA wL (q + 1)
  obtain ⟨hpol⟩ := hpol
  obtain ⟨hquot⟩ := hquot
  obtain ⟨hlower⟩ := hlower
  let := hcollapse
  exact ⟨hpol.symm ≪≫ hquot.symm ≪≫ (asIso (SSetPair.homologyMap (GoodPair.collapseSingularPairMap (TopCat.of D) A) R0 (q + 1))).symm ≪≫ hshiftq ≪≫ hlower⟩

end HolomorphicAnosov
