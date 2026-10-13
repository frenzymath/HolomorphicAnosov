import HolomorphicAnosov.Topology.AugmentedRelativeChains

/-! Source: Hatcher, *Algebraic Topology*, p.118 (augmented relative chains)
and p.124 (collapse naturality). DAG node: `topo.def_augmented_relative_projection`. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits Set
open scoped ZeroObject
namespace HolomorphicAnosov.GoodPair
universe u

/-- The literal augmented quotient projection, zero on the added integers.
Source: Hatcher p.118. The chain-map square in degree 1→0 is zero on both
sides, while every successor square is the native relative projection square. -/
def augmentedRelativeProjection (X : TopCat.{u}) (A : Set X) :
    augmentedIntegralSingularChains X ⟶ augmentedRelativeChains X A :=
  ChainComplex.ofHom
    (fun n ↦ match n with
      | 0 => 0
      | n + 1 => ((singularSubspacePair X A).chainComplexπ
          reducedSingularIntegralCoefficients).f n)
    (fun n ↦ by
      cases n with
      | zero =>
          change _ ≫ (0 : _ ⟶ (0 : ModuleCat.{u} ℤ)) = _ ≫ 0
          exact comp_zero.trans comp_zero.symm
      | succ n => exact ((singularSubspacePair X A).chainComplexπ
          reducedSingularIntegralCoefficients).comm (n + 1) n)

end HolomorphicAnosov.GoodPair

