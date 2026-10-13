import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.SheetProjectionInjective

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem sheet_projection_surjective {X : Type*} [TopologicalSpace X] {b : X}
    {U : Set X} (hU : GoodSet U) (a : PathCover b) (ha : a.1 ∈ U) :
    (fun e : PathCover b ↦ e.1) '' PathSheet U a = U := by
  apply Subset.antisymm
  · rintro x ⟨e, he, rfl⟩
    exact sheet_endpoint_mem he
  · intro y hy
    let η := (hU.2.1.joinedIn a.1 ha y hy).somePath
    exact ⟨⟨y, a.2.trans (Path.Homotopic.Quotient.mk η)⟩, ⟨η, (hU.2.1.joinedIn a.1 ha y hy).somePath_mem, rfl⟩, rfl⟩



end
end HolomorphicAnosov
