import HolomorphicAnosov.Topology.DegreeOneHurewiczHom
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Group.TypeTags.Hom

noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- The canonical additive homomorphism from the abelianization, with actual
data obtained by Mathlib's quotient lift. Source: Hatcher, p. 167. -/
def degreeOneHurewiczAbelianized {X : Type u} [TopologicalSpace X] (x : X) :
    Additive (Abelianization (FundamentalGroup X x)) →+ IntegralSingularH1 X :=
  (Abelianization.lift (degreeOneHurewicz x)).toAdditiveLeft

end HolomorphicAnosov.Topology
