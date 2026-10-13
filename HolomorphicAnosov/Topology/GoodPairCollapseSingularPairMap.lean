import HolomorphicAnosov.Topology.GoodPairCollapseMorphism
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex

/-! The collapse map of singular pairs. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits Set
open scoped ZeroObject
namespace HolomorphicAnosov.GoodPair
universe u

/-- The quotient map of singular pairs `(X,A) → (X/A,A/A)`, with its subspace image. (Hatcher, Prop. 2.22) -/
def collapseSingularPairMap (X : TopCat.{u}) (A : Set X) :
    singularSubspacePair X A ⟶
      singularSubspacePair (TopCat.of (Collapsed A)) (collapsedPart A) :=
  singularSubspacePairMap (collapseMorphism X A) A (collapsedPart A)
    (fun x hx ↦ ⟨x, hx, rfl⟩)

end HolomorphicAnosov.GoodPair

