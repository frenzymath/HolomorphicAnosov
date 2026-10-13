import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.StoppedClassTrans

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

def stoppedLift {X : Type*} [TopologicalSpace X] {b x : X}
    (α : Path b x) (t : unitInterval) : PathCover b := ⟨α t, stoppedClass α t⟩



end
end HolomorphicAnosov
