import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.SheetsBasis

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem endpoint_continuous {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (b : X)
    (hsemi : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ p : Path x x, (∀ t, p t ∈ U) → p.Homotopic (Path.refl x)) :
    letI := pathCoverTopology b
    Continuous (fun e : PathCover b ↦ e.1) := by
  let _ := pathCoverTopology b
  rw [continuous_def]
  intro O hO
  rw [isOpen_iff_mem_nhds]
  intro e he
  obtain ⟨U, hU, heU, hsub⟩ := good_neighborhood hsemi e.1 hO he
  exact Filter.mem_of_superset
    ((sheets_basis b hsemi).mem_nhds ⟨U, e, hU, heU, rfl⟩ (self_mem_sheet heU))
    (fun d hd ↦ hsub (sheet_endpoint_mem hd))



end
end HolomorphicAnosov
