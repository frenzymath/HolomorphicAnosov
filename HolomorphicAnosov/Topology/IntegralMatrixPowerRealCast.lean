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

/-- Integer matrix powers commute with real coordinate inclusion, in the literal
row/mulVec convention used by the normalized torus loops. -/
theorem integral_matrix_power_real_cast (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) (z : Fin n → ℤ) :
    (fun i ↦ (((A.mulVecLin ^ m) z) i : ℝ)) =
      ((A.map (Int.castRingHom ℝ)).mulVecLin ^ m) (fun i ↦ (z i : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ']
    change (fun i ↦ (((A.mulVec ((A.mulVecLin ^ m) z)) i) : ℝ)) =
      (A.map (Int.castRingHom ℝ)).mulVec
        (((A.map (Int.castRingHom ℝ)).mulVecLin ^ m) (fun i ↦ (z i : ℝ)))
    rw [← ih]
    ext i
    simp [Matrix.mulVec, dotProduct]


end HolomorphicAnosov.Topology
