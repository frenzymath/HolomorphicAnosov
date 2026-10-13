import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.SheetRecenter

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem sheet_mono {X : Type*} [TopologicalSpace X] {b : X}
    {U V : Set X} {a : PathCover b} (h : U ⊆ V) : PathSheet U a ⊆ PathSheet V a := by
  rintro e ⟨η, hη, he⟩
  exact ⟨η, fun t ↦ h (hη t), he⟩



end
end HolomorphicAnosov
