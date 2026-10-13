import HolomorphicAnosov.Topology.Homology.ModTwoAugmentedPairShortExact
import HolomorphicAnosov.Topology.Homology.ModTwoAugmentedContractibleAcyclic
import HolomorphicAnosov.Topology.Homology.ModTwoAugmentedDegreeZero
import HolomorphicAnosov.Topology.Homology.ZeroAugmentHomologyIso
import Mathlib.Algebra.Homology.HomologySequence

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial ZeroObject
namespace HolomorphicAnosov

set_option backward.isDefEq.respectTransparency false in
/-- Relative homology modulo a contractible subspace is the reduced homology
of the ambient space over the literal mod-two coefficient module. In particular
this applies to every nonempty singleton subspace, with no good-pair assumption.

Source: Hatcher, Algebraic Topology, augmented pair sequence p.118 and arbitrary
coefficients p.153. The augmented pair short exact sequence gives the actual
quotient projection. All augmented homology groups of the subspace vanish:
positive indices by contractibility, and index zero by nonemptiness and the
surjective coefficient-sum augmentation. Exactness on either side of the
projection in the homology sequence makes its induced map monic and epic,
hence invertible. Augmentation by zero identifies its target with ordinary
relative homology, including degree zero. No closedness or neighborhood
retraction is required for this relative-to-reduced comparison. -/
theorem modTwoContractibleSubspaceComparison (X : TopCat.{0}) (A : Set X)
    [ContractibleSpace A] :
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    let P := singularSubspacePair X A
    let KA := P.left.chainComplex R0
    let KX := P.right.chainComplex R0
    let εA : KA.X 0 ⟶ R0 := Sigma.desc (fun _ : P.left _⦋0⦌ ↦ 𝟙 R0)
    let εX : KX.X 0 ⟶ R0 := Sigma.desc (fun _ : P.right _⦋0⦌ ↦ 𝟙 R0)
    ∀ (_wA : KA.d 1 0 ≫ εA = 0) (wX : KX.d 1 0 ≫ εX = 0),
    let RX := ChainComplex.augment KX εX wX
    ∀ n : ℕ, Nonempty (P.homology R0 n ≅ RX.homology (n + 1)) := by
  dsimp only
  intro wA wX
  obtain ⟨i, π, h, hS, _, _, _⟩ := modTwoAugmentedPairShortExact X A wA wX
  let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
  let P := singularSubspacePair X A
  let KA := P.left.chainComplex R0
  let εA : KA.X 0 ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
  let RA := ChainComplex.augment KA εA wA
  have hz (n : ℕ) : IsZero (RA.homology n) := by
    cases n with
    | zero => exact modTwoAugmentedDegreeZero (TopCat.of A) wA
    | succ n => exact modTwoAugmentedContractibleAcyclic (TopCat.of A) wA n
  have hiso (n : ℕ) : IsIso (HomologicalComplex.homologyMap π (n + 1)) := by
    have : Mono (HomologicalComplex.homologyMap π (n + 1)) :=
      (hS.homology_exact₂ (n + 1)).mono_g ((hz (n + 1)).eq_of_src _ _)
    have : Epi (HomologicalComplex.homologyMap π (n + 1)) :=
      (hS.homology_exact₃ (n + 1) n (by simp)).epi_f ((hz n).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _
  intro n
  have := hiso n
  exact ⟨(asIso (HomologicalComplex.homologyMap π (n + 1)) ≪≫
    zeroAugmentHomologyIso (P.chainComplex R0) n).symm⟩

end HolomorphicAnosov
