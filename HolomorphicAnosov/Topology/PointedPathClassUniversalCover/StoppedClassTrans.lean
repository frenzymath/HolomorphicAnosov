import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.StoppedClass

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem stoppedClass_trans {X : Type*} [TopologicalSpace X] {b x : X}
    (α : Path b x) (t s : unitInterval) :
    (stoppedClass α t).trans (mk (α.subpath t s)) = stoppedClass α s := by
  have h := Path.Homotopic.Quotient.eq.mpr
    (show ((α.subpath 0 t).trans (α.subpath t s)).Homotopic (α.subpath 0 s) from
      ⟨Path.Homotopy.subpathTransSubpath α 0 t s⟩)
  have hc := congrArg (fun q : Path.Homotopic.Quotient (α 0) (α s) ↦
    q.cast α.source.symm rfl) h
  simpa only [stoppedClass, ← mk_trans, ← mk_cast, Path.cast_trans, Path.cast_rfl_rfl] using hc

end
end HolomorphicAnosov
