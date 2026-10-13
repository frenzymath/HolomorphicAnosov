import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.EndpointCovering

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem cover_locallyPathConnected {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (b : X)
    (hsemi : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ p : Path x x, (∀ t, p t ∈ U) → p.Homotopic (Path.refl x)) :
    letI := pathCoverTopology b
    LocallyPathConnectedSpace (PathCover b) := by
  let _ := pathCoverTopology b
  apply LocallyPathConnectedSpace.of_bases (fun _ ↦ (sheets_basis b hsemi).nhds_hasBasis)
  rintro e S ⟨⟨U, a, hU, ha, rfl⟩, he⟩
  have : PathConnectedSpace U := isPathConnected_iff_pathConnectedSpace.mp hU.2.1
  exact isPathConnected_iff_pathConnectedSpace.mpr
    (sheetHomeomorph b hsemi hU a ha).symm.pathConnectedSpace



end
end HolomorphicAnosov
