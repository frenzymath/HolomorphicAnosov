import HolomorphicAnosov.Linear.HyperbolicRealSplitting
import HolomorphicAnosov.Topology.InvertibleLinearLocalDegree
import HolomorphicAnosov.Topology.TorusStandardWinding
import HolomorphicAnosov.Topology.EuclideanFixedPointIndex
import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Homotopy.Path
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Algebra.Module.ZLattice.Basic

/-! Public auxiliary result used by torus lift fixed-point existence. -/

universe u

noncomputable section

open scoped ContDiff

namespace HolomorphicAnosov.Topology

/-- A central deck displacement is determined by its monodromy at one fibre point. -/
theorem monodromy_deck_of_one
    {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [AddCommGroup G] [AddAction G E] {p : E → X}
    (hp : IsAddQuotientCoveringMap p G) {x : X}
    (β : Path.Homotopic.Quotient x x) (k : G) (e0 : p ⁻¹' {x})
    (h : hp.isCoveringMap.monodromy β e0 = hp.toMultiplicative.toPermFiber x k e0) :
    ∀ e, hp.isCoveringMap.monodromy β e = hp.toMultiplicative.toPermFiber x k e := by
  intro e
  obtain ⟨d, rfl⟩ := hp.toMultiplicative.exists_toPermFiber_eq e0 e
  rw [hp.toMultiplicative.monodromy_toPermFiber, h]
  have hc : Commute d (Multiplicative.ofAdd k) := Commute.all _ _
  exact congrArg (fun a : Equiv.Perm (p ⁻¹' {x}) ↦ a e0) ((map_mul (hp.toMultiplicative.toPermFiber x) d (Multiplicative.ofAdd k)).symm.trans
    ((congrArg (hp.toMultiplicative.toPermFiber x) hc.eq).trans
      (map_mul (hp.toMultiplicative.toPermFiber x) (Multiplicative.ofAdd k) d)))


end HolomorphicAnosov.Topology
