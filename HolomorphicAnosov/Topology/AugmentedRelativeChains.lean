import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex

/-! Source: Hatcher, *Algebraic Topology*, p.118 (augmented relative chains)
and p.124 (collapse naturality). DAG node: `topo.def_augmented_relative_chains`. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits Set
open scoped ZeroObject
namespace HolomorphicAnosov.GoodPair
universe u

/-- Relative chains shifted to the augmented grading, with zero in degree −1.
Source: Hatcher p.118, the augmented pair sequence. The differential to the
added zero module is the zero map; successor differentials are the original
relative singular differentials. -/
def augmentedRelativeChains (X : TopCat.{u}) (A : Set X) :
    ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ChainComplex.augment
    ((singularSubspacePair X A).chainComplex reducedSingularIntegralCoefficients)
    (0 : ((singularSubspacePair X A).chainComplex
      reducedSingularIntegralCoefficients).X 0 ⟶ 0) (by exact comp_zero)

end HolomorphicAnosov.GoodPair

