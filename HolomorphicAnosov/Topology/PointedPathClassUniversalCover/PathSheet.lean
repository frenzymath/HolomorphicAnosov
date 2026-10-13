import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.GoodSet

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

def PathSheet {X : Type*} [TopologicalSpace X] {b : X}
    (U : Set X) (a : PathCover b) : Set (PathCover b) :=
  {e | ∃ η : Path a.1 e.1, (∀ t, η t ∈ U) ∧ a.2.trans (Path.Homotopic.Quotient.mk η) = e.2}



end
end HolomorphicAnosov
