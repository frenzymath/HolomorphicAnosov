import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.EndpointContinuous

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem endpoint_open {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (b : X)
    (hsemi : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ p : Path x x, (∀ t, p t ∈ U) → p.Homotopic (Path.refl x)) :
    letI := pathCoverTopology b
    IsOpenMap (fun e : PathCover b ↦ e.1) := by
  let _ := pathCoverTopology b
  intro O hO
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨e, he, rfl⟩
  obtain ⟨S, ⟨U, a, hU, ha, rfl⟩, heS, hsub⟩ :=
    (sheets_basis b hsemi).exists_subset_of_mem_open he hO
  exact Filter.mem_of_superset (hU.1.mem_nhds (sheet_endpoint_mem heS))
    (fun y hy ↦ by
      obtain ⟨d, hd, hdy⟩ := (sheet_projection_surjective hU a ha).symm.subset hy
      exact ⟨d, hsub hd, hdy⟩)



end
end HolomorphicAnosov
