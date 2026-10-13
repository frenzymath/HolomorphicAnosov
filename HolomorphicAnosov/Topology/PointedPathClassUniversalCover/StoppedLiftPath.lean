import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.StoppedLiftOne

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

def stoppedLiftPath {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] {b x : X}
    (hsemi : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ p : Path x x, (∀ t, p t ∈ U) → p.Homotopic (Path.refl x))
    (α : Path b x) :
    letI := pathCoverTopology b
    Path (⟨b, refl b⟩ : PathCover b) ⟨x, mk α⟩ := by
  letI := pathCoverTopology b
  exact ⟨⟨stoppedLift α, stoppedLift_continuous hsemi α⟩,
    stoppedLift_zero α, stoppedLift_one α⟩



end
end HolomorphicAnosov
