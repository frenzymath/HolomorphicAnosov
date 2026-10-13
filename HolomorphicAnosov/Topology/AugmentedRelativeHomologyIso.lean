import HolomorphicAnosov.Topology.AugmentedRelativeChains
import HolomorphicAnosov.Topology.ZeroAugmentHomologyIso

/-! Source: Hatcher, *Algebraic Topology*, p.118 (augmented relative chains)
and p.124 (collapse naturality). DAG node: `topo.def_augmented_relative_homology_iso`. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace HolomorphicAnosov.GoodPair
universe u
/-- The actual augmented relative homology identifies with native relative
homology in every nonnegative mathematical degree. Source: Hatcher p.118. -/
def augmentedRelativeHomologyIso (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    (augmentedRelativeChains X A).homology (n + 1) ≅
      (singularSubspacePair X A).homology reducedSingularIntegralCoefficients n :=
  zeroAugmentHomologyIso _ n


end HolomorphicAnosov.GoodPair

