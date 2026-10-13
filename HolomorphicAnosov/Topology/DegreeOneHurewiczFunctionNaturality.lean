import HolomorphicAnosov.Topology.IntegralSingularH1Map
import HolomorphicAnosov.Topology.LoopSingularClassMap
import HolomorphicAnosov.Topology.DegreeOneHurewiczFunction

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u
namespace HolomorphicAnosov.Topology

/-- The degree-one Hurewicz function commutes with based continuous maps.
Source: Hatcher, Algebraic Topology, p.168. Replace the target basepoint using
its prescribed equality, represent the fundamental-group element by a loop,
and use naturality of the native loop cycle class. No path-connectedness is
needed for this equality. -/
theorem degreeOneHurewiczFunction_naturality
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (g : C(X, Y)) (hg : g x = y) (a : FundamentalGroup X x) :
    degreeOneHurewiczFunction y (FundamentalGroup.mapOfEq g hg a) =
      integralSingularH1Map g (degreeOneHurewiczFunction x a) := by
  subst y
  induction a using Quotient.inductionOn with
  | h α =>
    rw [FundamentalGroup.mapOfEq_apply]
    change loopSingularClass (α.map g.continuous) = integralSingularH1Map g (loopSingularClass α)
    exact (loopSingularClass_map α g).symm
end HolomorphicAnosov.Topology
