import HolomorphicAnosov.Topology.IntegralSingularH1
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Group.TypeTags.Hom

noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- The ordinary singular H1 map of an actual continuous map.
Source: Hatcher, p. 168; the body is the native singular homology functor. -/
def integralSingularH1Map {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (g : C(X, Y)) : IntegralSingularH1 X →ₗ[ℤ] IntegralSingularH1 Y :=
  (((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj
    (ModuleCat.of ℤ (ULift.{u} ℤ))).map (TopCat.ofHom g)).hom

end HolomorphicAnosov.Topology
