import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.PrefixFree

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem prefix_orbit {X : Type*} [TopologicalSpace X] {b : X} (e d : PathCover b) :
    e.1 = d.1 ↔ ∃ γ : (FundamentalGroup X b)ᵐᵒᵖ, d = prefixEquiv b γ e := by
  rcases e with ⟨x, α⟩
  rcases d with ⟨y, β⟩
  constructor
  · intro h
    dsimp at h
    subst y
    refine ⟨MulOpposite.op (β.trans α.symm), ?_⟩
    simp [prefixEquiv]
  · rintro ⟨γ, he⟩
    exact (congrArg Sigma.fst he).symm



end
end HolomorphicAnosov
