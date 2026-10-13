import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.SheetHomeomorphEndpoint

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

def prefixEquiv {X : Type*} [TopologicalSpace X] (b : X)
    (γ : (FundamentalGroup X b)ᵐᵒᵖ) : PathCover b ≃ PathCover b where
  toFun e := ⟨e.1, γ.unop.trans e.2⟩
  invFun e := ⟨e.1, γ.unop.symm.trans e.2⟩
  left_inv e := by cases e; simp [← trans_assoc]
  right_inv e := by cases e; simp [← trans_assoc]



end
end HolomorphicAnosov
