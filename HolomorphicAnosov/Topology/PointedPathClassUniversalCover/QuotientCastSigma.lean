import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.ReflCastSigma

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem quotient_cast_sigma {X : Type*} [TopologicalSpace X] {a b c : X}
    (q : Path.Homotopic.Quotient a b) (h : c = b) :
    (⟨c, q.cast rfl h⟩ : PathCover a) = ⟨b, q⟩ := by
  subst c
  simp



end
end HolomorphicAnosov
