import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.PrefixOrbit

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

def prefixDeckAction {X : Type*} [TopologicalSpace X] (b : X) :
    letI := pathCoverTopology b
    (FundamentalGroup X b)ᵐᵒᵖ →* deck (fun e : PathCover b ↦ e.1) := by
  letI := pathCoverTopology b
  refine { toFun := (fun γ ↦ ⟨prefixHomeomorph b γ, rfl⟩)
           map_one' := ?_
           map_mul' := ?_ }
  · apply Subtype.ext
    apply Homeomorph.ext
    intro e
    change prefixEquiv b 1 e = e
    cases e with
    | mk x α =>
      apply congrArg (Sigma.mk x)
      exact refl_trans α
  · intro γ δ
    apply Subtype.ext
    apply Homeomorph.ext
    intro e
    change prefixEquiv b (γ * δ) e = prefixEquiv b γ (prefixEquiv b δ e)
    cases e with
    | mk x α =>
      apply congrArg (Sigma.mk x)
      exact trans_assoc γ.unop δ.unop α



end
end HolomorphicAnosov
