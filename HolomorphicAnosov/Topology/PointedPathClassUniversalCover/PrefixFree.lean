import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.PrefixHomeomorph

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem prefix_free {X : Type*} [TopologicalSpace X] {b : X}
    (γ : (FundamentalGroup X b)ᵐᵒᵖ) (e : PathCover b)
    (he : prefixEquiv b γ e = e) : γ = 1 := by
  cases e with
  | mk x α =>
    have hc : γ.unop.trans α = α := eq_of_heq (Sigma.mk.inj he).2
    have hh := congrArg (fun q : Path.Homotopic.Quotient b x ↦ q.trans α.symm) hc
    have hγ : γ.unop = Path.Homotopic.Quotient.refl b := by simpa using hh
    apply MulOpposite.unop_injective
    exact hγ

end
end HolomorphicAnosov
