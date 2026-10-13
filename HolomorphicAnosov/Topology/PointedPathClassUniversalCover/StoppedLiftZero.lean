import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.QuotientCastSigma

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem stoppedLift_zero {X : Type*} [TopologicalSpace X] {b x : X}
    (α : Path b x) : stoppedLift α 0 = ⟨b, refl b⟩ := by
  simp only [stoppedLift, stoppedClass, Path.subpath_self]
  exact refl_cast_sigma α.source



end
end HolomorphicAnosov
