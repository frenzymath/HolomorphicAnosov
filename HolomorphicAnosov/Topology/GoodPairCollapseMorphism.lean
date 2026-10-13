import HolomorphicAnosov.Topology.GoodPairCollapse
import Mathlib.Topology.Category.TopCat.Basic

/-! The collapse quotient projection as a topological morphism. -/

noncomputable section

open CategoryTheory

namespace HolomorphicAnosov.GoodPair

universe u

/-- The quotient projection as a topological morphism, with the native collapse quotient topology. (Hatcher, Prop. 2.22) -/
def collapseMorphism (X : TopCat.{u}) (A : Set X) : X ⟶ TopCat.of (Collapsed A) :=
  TopCat.ofHom (collapse A)

end HolomorphicAnosov.GoodPair
