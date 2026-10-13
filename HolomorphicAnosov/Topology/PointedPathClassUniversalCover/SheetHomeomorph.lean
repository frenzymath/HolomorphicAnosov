import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.EndpointOpen

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

def sheetHomeomorph {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (b : X)
    (hsemi : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ p : Path x x, (∀ t, p t ∈ U) → p.Homotopic (Path.refl x))
    {U : Set X} (hU : GoodSet U) (a : PathCover b) (ha : a.1 ∈ U) :
    letI := pathCoverTopology b
    PathSheet U a ≃ₜ U := by
  letI := pathCoverTopology b
  let F : PathSheet U a → U := fun e ↦ ⟨e.val.1, sheet_endpoint_mem e.property⟩
  have hF : Bijective F := by
    constructor
    · intro e d h
      apply Subtype.ext
      exact sheet_projection_injective hU a e.property d.property (congrArg Subtype.val h)
    · intro y
      obtain ⟨e, he, hey⟩ := (sheet_projection_surjective hU a ha).symm.subset y.property
      exact ⟨⟨e, he⟩, Subtype.ext hey⟩
  have hc : Continuous F :=
    ((endpoint_continuous b hsemi).comp continuous_subtype_val).subtype_mk _
  have ho : IsOpenMap F :=
    ((endpoint_open b hsemi).comp
      ((sheets_basis b hsemi).isOpen ⟨U, a, hU, ha, rfl⟩).isOpenEmbedding_subtypeVal.isOpenMap).subtype_mk _
  exact (Equiv.ofBijective F hF).toHomeomorphOfContinuousOpen hc ho

end
end HolomorphicAnosov
