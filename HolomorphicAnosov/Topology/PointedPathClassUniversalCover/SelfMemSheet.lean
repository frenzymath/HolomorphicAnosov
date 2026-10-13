import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.GoodPathEq

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem self_mem_sheet {X : Type*} [TopologicalSpace X] {b : X}
    {U : Set X} {a : PathCover b} (ha : a.1 ∈ U) : a ∈ PathSheet U a := by
  exact ⟨Path.refl a.1, by simpa using fun _ : unitInterval ↦ ha, by simp⟩

end
end HolomorphicAnosov
