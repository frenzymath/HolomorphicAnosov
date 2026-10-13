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

/-- Iterating a chosen one-step lift with its proved deck law gives the literal
integer matrix power deck law, before comparing with an arbitrary chosen iterate lift. -/
theorem iterate_coordinate_deck_covariance (n : ℕ)
    (H : (Fin n → ℝ) → (Fin n → ℝ)) (A : Matrix (Fin n) (Fin n) ℤ)
    (hH : ∀ v (z : Fin n → ℤ), H (v + fun i ↦ (z i : ℝ)) =
      H v + fun i ↦ (A.mulVec z i : ℝ)) (m : ℕ) :
    ∀ v (z : Fin n → ℤ), H^[m] (v + fun i ↦ (z i : ℝ)) =
      H^[m] v + fun i ↦ ((A.mulVecLin ^ m) z i : ℝ) := by
  induction m with
  | zero => intro v z; simp
  | succ m ih =>
    intro v z
    rw [Function.iterate_succ_apply', ih, hH, pow_succ', Function.iterate_succ_apply']
    rfl


end HolomorphicAnosov.Topology
