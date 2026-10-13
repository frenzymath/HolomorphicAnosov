import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.EndpointSurjective

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem endpoint_covering {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] [PathConnectedSpace X] (b : X)
    (hsemi : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ p : Path x x, (∀ t, p t ∈ U) → p.Homotopic (Path.refl x)) :
    letI := pathCoverTopology b
    IsCoveringMap (fun e : PathCover b ↦ e.1) := by
  let _ := pathCoverTopology b
  let _ : MulAction (FundamentalGroup X b)ᵐᵒᵖ (PathCover b) :=
    MulAction.compHom (PathCover b) (prefixDeckAction b)
  have hq : IsQuotientCoveringMap (fun e : PathCover b ↦ e.1)
      (FundamentalGroup X b)ᵐᵒᵖ := by
    refine { toIsQuotientMap := ((endpoint_open b hsemi).isQuotientMap
                 (endpoint_continuous b hsemi) (endpoint_surjective b))
             continuous_const_smul := ?_
             apply_eq_iff_mem_orbit := ?_
             disjoint := ?_ }
    · intro γ
      exact (prefixHomeomorph b γ).continuous
    · intro e d
      rw [MulAction.mem_orbit_iff]
      constructor
      · intro h
        obtain ⟨γ, hγ⟩ := (prefix_orbit d e).mp h.symm
        exact ⟨γ, hγ.symm⟩
      · rintro ⟨γ, hγ⟩
        exact (congrArg Sigma.fst hγ).symm
    · intro e
      obtain ⟨U, hU, heU, _⟩ := good_neighborhood hsemi e.1 isOpen_univ (mem_univ _)
      refine ⟨PathSheet U e,
        (sheets_basis b hsemi).mem_nhds ⟨U, e, hU, heU, rfl⟩ (self_mem_sheet heU), ?_⟩
      intro γ hmeet
      rcases hmeet with ⟨d, ⟨a, ha, had⟩, hd⟩
      change prefixEquiv b γ a = d at had
      have hga : prefixEquiv b γ a ∈ PathSheet U e := had.symm ▸ hd
      have hSame : prefixEquiv b γ a = a :=
        sheet_projection_injective hU e hga ha rfl
      exact prefix_free γ a hSame
  exact hq.isCoveringMap



end
end HolomorphicAnosov
