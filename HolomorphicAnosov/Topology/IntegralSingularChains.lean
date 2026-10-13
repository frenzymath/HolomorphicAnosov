import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- Ordinary integral singular chains, with the universe-lifted integer module.
Source: Hatcher, pp. 108–109; the body is Mathlib's singular-set chain complex. -/
abbrev integralSingularChains (X : Type u) [TopologicalSpace X] :
    ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))

end HolomorphicAnosov.Topology

