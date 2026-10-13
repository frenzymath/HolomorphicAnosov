import HolomorphicAnosov.Topology.Homology.ModTwoConnectedReducedH0
import HolomorphicAnosov.Topology.Homology.ModTwoPositiveSphereReducedH0
import HolomorphicAnosov.Topology.Homology.ModTwoPositiveSphereProfileBase
import HolomorphicAnosov.Topology.Homology.ModTwoPositiveSphereProfileStep
import HolomorphicAnosov.Topology.Homology.ModTwoSphereSuccessor
import HolomorphicAnosov.Topology.Homology.ModTwoAugmentedHomeomorphIso
import HolomorphicAnosov.Topology.Homology.ModTwoContractibleAmbientShift
import HolomorphicAnosov.Topology.Homology.ModTwoContractibleSubspaceComparison
import HolomorphicAnosov.Topology.Homology.ModTwoGoodPairCollapse
import HolomorphicAnosov.Topology.Homology.ModTwoAugmentedContractibleAcyclic
import HolomorphicAnosov.Topology.Homology.ModTwoAugmentedPairShortExact
import HolomorphicAnosov.Topology.Homology.ModTwoZeroSphereProfile
import HolomorphicAnosov.Topology.Homology.ModTwoDiskBoundaryConnectingPositive
import HolomorphicAnosov.Topology.Homology.ModTwoTwoPointAugmentationKernel
import HolomorphicAnosov.Topology.Homology.ModTwoAugmentedDiscreteHomology
import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairComplementHomeomorphism
import HolomorphicAnosov.Topology.GoodPairDeformationRelativeAcyclicity
import HolomorphicAnosov.Topology.GoodPairNeighborhoodQuotientImage
import HolomorphicAnosov.Topology.GoodPairQuotientHomotopyDescentG8
import HolomorphicAnosov.Topology.RelativeSingularHomotopyInvariance
import HolomorphicAnosov.Topology.SingularHomologyExcision
import Mathlib.Analysis.InnerProductSpace.PiL2

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov

/-- Positive-dimensional unit spheres have the fixed mod-two coefficient object
in their top reduced degree and zero in every other nonnegative degree.

Source: Hatcher, Algebraic Topology, Corollary 2.14 and Theorem 2.13 p.114;
Propositions 2.6–2.8 pp.109–110; relative exactness pp.115–118; the excision and
good-pair comparison pp.119–124; coefficient extension p.153.

Proof: Work with singular chains with the literal coefficient object R0 and
coefficient-sum augmentation; reduced degree q is augmented homology in degree q+1.
For S⁰ the singular complex is the two-point alternating constant complex. Its
augmentation kernel consists of pairs (a,-a), isomorphic to R0, and every higher
reduced group is zero. A disk contracts to its center. Extend the singular prism
homotopy by zero in augmented degree zero; the constant map factors through the
acyclic augmented point complex, so the disk has zero reduced homology.
For d>0 the sphere boundary A of Dᵈ is a nonempty closed subspace, and the collar
norm(x)>1/2 strongly retracts onto A by ((1-t)+t/norm(x))x. The inclusion of
augmented chains is degreewise monic; its cokernel is the shifted relative complex.
Excision in this collar and in its quotient identifies H_q(Dᵈ,A;R0) with
reduced H_q(Dᵈ/A;R0). The quotient is Sᵈ: the polar map sends x of radius ρ>0 to
(sin(πρ)x/ρ,cos(πρ)), sends zero to the north pole, and collapses the boundary to
the south pole. Its induced continuous bijection is a homeomorphism by compactness.
The augmented pair exact sequence has zero disk terms, yielding reduced
H_(q+1)(Sᵈ;R0) ≅ reduced H_q(S^(d-1);R0) for q≥0 and reduced H_0(Sᵈ;R0)=0.
Induction from the two-point calculation proves the statement in every degree.
The connecting map at q=0 lands in the augmentation kernel, not ordinary H_0.
Hatcher p.153 explicitly carries these proofs over to arbitrary coefficient
groups; no tensoring or flatness assertion is used. The witness w only certifies
the boundary/augmentation equation and is unique by proof irrelevance. -/
theorem modTwoPositiveUnitSphereProfile (k : ℕ) :
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    let S := {x : EuclideanSpace ℝ (Fin (k + 1 + 1)) // ‖x‖ = 1}
    let L := TopCat.toSSet.obj (TopCat.of S)
    let K := L.chainComplex R0
    let ε : K.X 0 ⟶ R0 := Sigma.desc (fun _ : L _⦋0⦌ ↦ 𝟙 R0)
    ∀ w : K.d 1 0 ≫ ε = 0,
      Nonempty ((ChainComplex.augment K ε w).homology (k + 1 + 1) ≅ R0) ∧
      ∀ q : ℕ, q ≠ k + 1 → IsZero ((ChainComplex.augment K ε w).homology (q + 1)) := by
  induction k with
  | zero =>
      simpa using modTwoPositiveSphereProfileBase
  | succ k ih =>
      simpa [Nat.add_assoc] using
        modTwoPositiveSphereProfileStep k
          (modTwoPositiveSphereReducedH0 (k + 1)) ih

end HolomorphicAnosov
