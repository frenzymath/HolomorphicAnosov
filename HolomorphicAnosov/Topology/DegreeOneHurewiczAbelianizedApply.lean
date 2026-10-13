import HolomorphicAnosov.Topology.LoopSingularClass
import HolomorphicAnosov.Topology.DegreeOneHurewiczAbelianized
import Mathlib.GroupTheory.Abelianization.Defs

noncomputable section
open CategoryTheory AlgebraicTopology
universe u
namespace HolomorphicAnosov.Topology

/-- The canonical abelianized Hurewicz map agrees with the loop class on each
abelianization generator.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 p.167; Mathlib's
`Abelianization.lift_apply_of`. -/
theorem degreeOneHurewiczAbelianized_apply_of
    {X : Type u} [TopologicalSpace X] {x : X} (α : Path x x) :
    degreeOneHurewiczAbelianized x
      (Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk α)))) = loopSingularClass α := by
  change degreeOneHurewicz x (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk α)) = _
  change degreeOneHurewiczFunction x (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk α)) = _
  rfl

end HolomorphicAnosov.Topology
