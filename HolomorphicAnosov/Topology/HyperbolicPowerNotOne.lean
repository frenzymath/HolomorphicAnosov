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

/-- Polynomial spectral mapping transfers the exact unit-circle exclusion to
the absence of one in EVERY positive power, including zero-dimensional spaces. -/
theorem hyperbolic_power_not_one (n : ℕ)
    (C : Module.End ℂ (Fin n → ℂ))
    (hC : ∀ μ : ℂ, C.HasEigenvalue μ → ‖μ‖ ≠ 1)
    (m : ℕ) (hm : 0 < m) : ¬ (C ^ m).HasEigenvalue 1 := by
  intro h
  have hs := Module.End.hasEigenvalue_iff_mem_spectrum.mp h
  rw [spectrum.map_pow_of_pos C hm] at hs
  obtain ⟨μ, hμ, hpow⟩ := hs
  have hnorm : ‖μ‖ ^ m = 1 := by simpa using congrArg norm hpow
  exact hC μ (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ)
    ((pow_eq_one_iff_of_nonneg (norm_nonneg μ) (Nat.ne_of_gt hm)).mp hnorm)


end HolomorphicAnosov.Topology
