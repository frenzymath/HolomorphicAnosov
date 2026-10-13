import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.StoppedLiftPath

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem cover_pathConnected {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (b : X)
    (hsemi : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ p : Path x x, (∀ t, p t ∈ U) → p.Homotopic (Path.refl x)) :
    letI := pathCoverTopology b
    PathConnectedSpace (PathCover b) := by
  let _ := pathCoverTopology b
  have hjoin : ∀ e : PathCover b, Joined (⟨b, refl b⟩ : PathCover b) e := by
    rintro ⟨x, q⟩
    obtain ⟨α, rfl⟩ := mk_surjective q
    exact ⟨stoppedLiftPath hsemi α⟩
  exact ⟨⟨⟨b, refl b⟩⟩, fun e d ↦ (hjoin e).symm.trans (hjoin d)⟩



end
end HolomorphicAnosov
