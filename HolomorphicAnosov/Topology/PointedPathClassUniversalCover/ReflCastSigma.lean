import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.StoppedLiftContinuous

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem refl_cast_sigma {X : Type*} [TopologicalSpace X] {a b : X}
    (h : a = b) :
    (⟨a, mk ((Path.refl a).cast h.symm rfl)⟩ : PathCover b) = ⟨b, refl b⟩ := by
  subst b
  simp [Path.cast_rfl_rfl, mk_refl]

end
end HolomorphicAnosov
