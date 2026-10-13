import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Logic.Function.Iterate

/-!
# Original asymptotic leaf carriers

Source: Shub, *Global Stability of Dynamical Systems* (1987), Definition 2.1,
pp.8–9, specialized to a singleton; Hirsch–Pugh–Shub, *Invariant Manifolds*,
§5, pp.61–62; Ghys, *Holomorphic Anosov systems*, §2, pp.588–589.
These are sets of original manifold points, not an existence or regularity theorem.
Their intrinsic leaf topology is separate from the ambient subtype topology.
-/

namespace HolomorphicAnosov

open Filter Topology _root_.Topology

variable {M : Type*} [MetricSpace M]

/-- Forward asymptoticity for the specified original map and metric.
Source: Shub Definition 2.1, pp.8–9, for the singleton consisting of `x`. -/
def ForwardAsymptotic (f : M → M) (x y : M) : Prop :=
  Tendsto (fun n : ℕ ↦ dist ((f^[n]) y) ((f^[n]) x)) atTop (𝓝 0)

/-- The original stable point set, with no specified intrinsic topology.
Source: Shub Definition 2.1, pp.8–9; HPS §5, pp.61–62. -/
abbrev StableAsymptoticLeaf (f : M ≃ₜ M) (x : M) :=
  {y : M // ForwardAsymptotic f x y}

/-- The original unstable point set uses literal forward iterates of the inverse.
Source: Shub Definition 2.1, pp.8–9; Ghys §2, pp.588–589. -/
abbrev UnstableAsymptoticLeaf (f : M ≃ₜ M) (x : M) :=
  StableAsymptoticLeaf f.symm x

end HolomorphicAnosov
