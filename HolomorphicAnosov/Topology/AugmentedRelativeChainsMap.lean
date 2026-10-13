import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative

/-! # Augmented relative chain map
Source: Hatcher, Algebraic Topology, pp.115–118: functoriality of relative chains
and the augmented pair sequence. The relative complex has the zero module in
mathematical degree −1, represented here by augmented index zero. Ordinary
relative degree `n` occupies augmented index `n + 1`.
DAG: topo.def_augmented_relative_chains_map.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HolomorphicAnosov.GoodPair
universe u

/-- Augmented relative map induced by a map of simplicial pairs, specialized
to the integral coefficient module used for singular homology.

Source: Hatcher, Algebraic Topology, p.118: a map of pairs induces the quotient
chain map, and relative chains have zero in the added degree −1. In augmented
index zero the component is the unique map between zero modules. In index
`n + 1` it is the native relative chain map in degree `n`. The first chain-map
square consists of zero composites; every later square is the corresponding
square of `SSetPair.chainComplexMap`. No nonemptiness assumption is needed for
this chain-map construction. -/
def augmentedRelativeChainsMap {P Q : SSetPair.{u}} (f : P ⟶ Q) :
    ChainComplex.augment (P.chainComplex reducedSingularIntegralCoefficients.{u})
      (0 : (P.chainComplex reducedSingularIntegralCoefficients.{u}).X 0 ⟶ 0) (by exact comp_zero) ⟶
    ChainComplex.augment (Q.chainComplex reducedSingularIntegralCoefficients.{u})
      (0 : (Q.chainComplex reducedSingularIntegralCoefficients.{u}).X 0 ⟶ 0) (by exact comp_zero) :=
  ChainComplex.ofHom
    (fun n ↦ match n with
      | 0 => 0
      | n + 1 => (SSetPair.chainComplexMap f reducedSingularIntegralCoefficients.{u}).f n)
    (fun n ↦ by
      cases n with
      | zero =>
          change _ ≫ (0 : _ ⟶ (0 : ModuleCat.{u} ℤ)) =
            (0 : _ ⟶ (0 : ModuleCat.{u} ℤ)) ≫ (0 : (0 : ModuleCat.{u} ℤ) ⟶ 0)
          exact comp_zero.trans comp_zero.symm
      | succ n => exact (SSetPair.chainComplexMap f reducedSingularIntegralCoefficients.{u}).comm (n + 1) n)
end HolomorphicAnosov.GoodPair

