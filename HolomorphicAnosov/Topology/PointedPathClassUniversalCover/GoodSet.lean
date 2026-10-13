import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.PathCover

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

def GoodSet {X : Type*} [TopologicalSpace X] (U : Set X) : Prop :=
  IsOpen U ∧ IsPathConnected U ∧ ∀ x ∈ U, ∀ p : Path x x,
    (∀ t, p t ∈ U) → p.Homotopic (Path.refl x)

end
end HolomorphicAnosov
