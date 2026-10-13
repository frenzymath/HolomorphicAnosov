import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.GoodNeighborhood

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

def sheetFamily {X : Type*} [TopologicalSpace X] (b : X) : Set (Set (PathCover b)) :=
  {S | ∃ (U : Set X) (a : PathCover b), GoodSet U ∧ a.1 ∈ U ∧ S = PathSheet U a}

end
end HolomorphicAnosov
