import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.SelfMemSheet

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem sheet_endpoint_mem {X : Type*} [TopologicalSpace X] {b : X}
    {U : Set X} {a e : PathCover b} (he : e ∈ PathSheet U a) : e.1 ∈ U := by
  rcases he with ⟨η, hη, _⟩
  simpa using hη 1



end
end HolomorphicAnosov
