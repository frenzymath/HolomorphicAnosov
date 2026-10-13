import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.PrefixDeckAction

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem endpoint_surjective {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    (b : X) : Surjective (fun e : PathCover b ↦ e.1) :=
  fun x ↦ ⟨⟨x, mk (PathConnectedSpace.somePath b x)⟩, rfl⟩



end
end HolomorphicAnosov
