import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.SheetFamily

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

@[instance_reducible]
def pathCoverTopology {X : Type*} [TopologicalSpace X] (b : X) :
    TopologicalSpace (PathCover b) := TopologicalSpace.generateFrom (sheetFamily b)



end
end HolomorphicAnosov
