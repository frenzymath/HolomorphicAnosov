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

/-- Endpoint conjugation is exactly path lifting and deck-translation commutation.
Source: Hatcher Theorem1.7 path/homotopy lifting and the based-change path argument.
This is private implementation for the actual lift consumer, not a new premise.
-/
theorem conjugated_monodromy_endpoint
    {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [AddCommGroup G] [AddAction G E] {p : E → X}
    (hp : IsAddQuotientCoveringMap p G) {x y : X}
    (c : Path.Homotopic.Quotient x y) (β : Path.Homotopic.Quotient y y)
    (k : G)
    (h : ∀ e0, hp.isCoveringMap.monodromy (c.trans (β.trans c.symm)) e0 =
      hp.toMultiplicative.toPermFiber x k e0) (e : p ⁻¹' {y}) :
    hp.isCoveringMap.monodromy β e = hp.toMultiplicative.toPermFiber y k e := by
  obtain ⟨e0, he0⟩ := (hp.isCoveringMap.monodromy_bijective c).surjective e
  apply (hp.isCoveringMap.monodromy_bijective c.symm).injective
  have hinv : hp.isCoveringMap.monodromy c.symm e = e0 := by
    rw [← he0, ← hp.isCoveringMap.monodromy_trans_apply, c.trans_symm,
      hp.isCoveringMap.monodromy_refl]
    rfl
  rw [hp.monodromy_toPermFiber, hinv]
  have hh := h e0
  rw [hp.isCoveringMap.monodromy_trans_apply,
    hp.isCoveringMap.monodromy_trans_apply, he0] at hh
  exact hh


end HolomorphicAnosov.Topology
