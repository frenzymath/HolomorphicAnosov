import HolomorphicAnosov.Topology.Homology.ModTwoAugmentedPairShortExact
import HolomorphicAnosov.Topology.Homology.ModTwoAugmentedContractibleAcyclic
import HolomorphicAnosov.Topology.Homology.ModTwoAugmentedDegreeZero
import HolomorphicAnosov.Topology.Homology.ZeroAugmentHomologyIso
import Mathlib.Algebra.Homology.HomologySequence

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial ZeroObject
namespace HolomorphicAnosov

/-- A nonempty subspace of a contractible space has its reduced mod-two
homology identified with relative homology one degree higher. Relative degree
zero vanishes separately, including when the subspace is disconnected.

Source: Hatcher, Algebraic Topology, augmented pair sequence p.118 and
arbitrary coefficients p.153. The two adjacent ambient reduced groups vanish,
so the connecting map in the augmented pair sequence is an isomorphism. The
zero-augmentation comparison turns its source into native relative homology.
For relative degree zero, the next term is augmented index zero of the
nonempty subspace, which vanishes. Thus the projection onto that relative
group is epic from zero, and the group is zero. In relative degree one the
target is reduced H0 of A, not ordinary H0. -/
theorem modTwoContractibleAmbientShift (X : TopCat.{0}) [ContractibleSpace X]
    (A : Set X) [Nonempty A] :
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    let P := singularSubspacePair X A
    let KA := P.left.chainComplex R0
    let KX := P.right.chainComplex R0
    let εA : KA.X 0 ⟶ R0 := Sigma.desc (fun _ : P.left _⦋0⦌ ↦ 𝟙 R0)
    let εX : KX.X 0 ⟶ R0 := Sigma.desc (fun _ : P.right _⦋0⦌ ↦ 𝟙 R0)
    ∀ (wA : KA.d 1 0 ≫ εA = 0) (_wX : KX.d 1 0 ≫ εX = 0),
    let RA := ChainComplex.augment KA εA wA
    IsZero (P.homology R0 0) ∧
      ∀ n : ℕ, Nonempty (P.homology R0 (n + 1) ≅ RA.homology (n + 1)) := by
  dsimp only
  intro wA wX
  obtain ⟨i, π, h, hS, _, _, _⟩ := modTwoAugmentedPairShortExact X A wA wX
  let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
  let P := singularSubspacePair X A
  have hzA := modTwoAugmentedDegreeZero (TopCat.of A) wA
  have hzX := modTwoAugmentedContractibleAcyclic X wX
  constructor
  · have : Epi (HomologicalComplex.homologyMap π 1) :=
      (hS.homology_exact₃ 1 0 (by simp)).epi_f (hzA.eq_of_tgt _ _)
    exact IsZero.of_iso (IsZero.of_epi (HomologicalComplex.homologyMap π 1) (hzX 0))
      (zeroAugmentHomologyIso (P.chainComplex R0) 0).symm
  · intro n
    have hrel : (ComplexShape.down ℕ).Rel (n + 2) (n + 1) := by simp
    have : IsIso (hS.δ (n + 2) (n + 1) hrel) :=
      hS.isIso_δ (n + 2) (n + 1) (by simp) (hzX (n + 1)) (hzX n)
    exact ⟨(zeroAugmentHomologyIso (P.chainComplex R0) (n + 1)).symm ≪≫
      asIso (hS.δ (n + 2) (n + 1) hrel)⟩

end HolomorphicAnosov
