import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.PrefixEquiv

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem prefix_sheet {X : Type*} [TopologicalSpace X] {b : X}
    (γ : (FundamentalGroup X b)ᵐᵒᵖ) (U : Set X) (a e : PathCover b) :
    prefixEquiv b γ e ∈ PathSheet U (prefixEquiv b γ a) ↔ e ∈ PathSheet U a := by
  constructor
  · rintro ⟨η, hη, he⟩
    refine ⟨η, hη, ?_⟩
    have hh := congrArg (fun q ↦ γ.unop.symm.trans q) he
    simpa [prefixEquiv, ← trans_assoc] using hh
  · rintro ⟨η, hη, he⟩
    refine ⟨η, hη, ?_⟩
    change (γ.unop.trans a.2).trans (mk η) = γ.unop.trans e.2
    rw [trans_assoc, he]

end
end HolomorphicAnosov
