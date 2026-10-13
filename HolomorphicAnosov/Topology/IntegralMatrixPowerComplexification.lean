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

/-- Real coordinate inclusion intertwines every power of the SAME integral matrix
with its complexification. -/
theorem integral_matrix_power_complexification (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) (v : Fin n → ℝ) :
    (fun i ↦ ((((A.map (Int.castRingHom ℝ)).mulVecLin ^ m) v) i : ℂ)) =
      ((A.map (Int.castRingHom ℂ)).mulVecLin ^ m) (fun i ↦ (v i : ℂ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ']
    change (fun i ↦ (((A.map (Int.castRingHom ℝ)).mulVec
      (((A.map (Int.castRingHom ℝ)).mulVecLin ^ m) v)) i : ℂ)) = _
    change (fun i ↦ (((A.map (Int.castRingHom ℝ)).mulVec
      (((A.map (Int.castRingHom ℝ)).mulVecLin ^ m) v)) i : ℂ)) =
      (A.map (Int.castRingHom ℂ)).mulVec
        (((A.map (Int.castRingHom ℂ)).mulVecLin ^ m) (fun i ↦ (v i : ℂ)))
    rw [← ih]
    ext i
    simp [Matrix.mulVec, dotProduct]


end HolomorphicAnosov.Topology
