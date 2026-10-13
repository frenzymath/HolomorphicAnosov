import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.StoppedLiftZero

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem stoppedLift_one {X : Type*} [TopologicalSpace X] {b x : X}
    (α : Path b x) : stoppedLift α 1 = ⟨x, mk α⟩ := by
  simp only [stoppedLift, stoppedClass, Path.subpath_zero_one, mk_cast]
  exact quotient_cast_sigma (mk α) α.target

end
end HolomorphicAnosov
