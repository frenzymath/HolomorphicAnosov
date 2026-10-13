import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.SheetMono

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem sheet_projection_injective {X : Type*} [TopologicalSpace X] {b : X}
    {U : Set X} (hU : GoodSet U) (a : PathCover b) :
    Set.InjOn (fun e : PathCover b ↦ e.1) (PathSheet U a) := by
  rintro ⟨x, α⟩ ⟨η, hη, hα⟩ ⟨y, β⟩ ⟨θ, hθ, hβ⟩ hxy
  dsimp at hxy
  subst y
  have hc := good_path_eq hU η θ hη hθ
  have hab : α = β := hα.symm.trans ((congrArg (fun q ↦ a.2.trans q) hc).trans hβ)
  exact congrArg (Sigma.mk x) hab



end
end HolomorphicAnosov
