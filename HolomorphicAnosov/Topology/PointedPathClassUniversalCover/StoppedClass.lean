import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.CoverLocallyPathConnected

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

def stoppedClass {X : Type*} [TopologicalSpace X] {b x : X}
    (α : Path b x) (t : unitInterval) : Path.Homotopic.Quotient b (α t) :=
  mk ((α.subpath 0 t).cast α.source.symm rfl)

end
end HolomorphicAnosov
