import HolomorphicAnosov.Topology.IntegralMatrixPowerComplexification
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

/-- Absence of the complex eigenvalue one makes the SAME real displacement
endomorphism invertible; no spectral classification hypothesis is added. -/
theorem real_displacement_equivalence (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ)
    (hA : ¬ Module.End.HasEigenvalue ((A.map (Int.castRingHom ℂ)).mulVecLin ^ m) 1) :
    ∃ L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ),
      ∀ v, L v = v - ((A.map (Int.castRingHom ℝ)).mulVecLin ^ m) v := by
  let B : Module.End ℝ (Fin n → ℝ) := (A.map (Int.castRingHom ℝ)).mulVecLin ^ m
  have hinj : Function.Injective ((LinearMap.id : Module.End ℝ (Fin n → ℝ)) - B) := by
    apply (LinearMap.ker_eq_bot (f := ((LinearMap.id : Module.End ℝ (Fin n → ℝ)) - B))).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    by_contra hne
    apply hA
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := fun i ↦ (v i : ℂ))
    constructor
    · rw [Module.End.mem_eigenspace_iff, one_smul]
      have hfix : B v = v := by
        have hh : v - B v = 0 := hv
        exact (sub_eq_zero.mp hh).symm
      rw [← integral_matrix_power_complexification, show
        ((A.map (Int.castRingHom ℝ)).mulVecLin ^ m) v = v from hfix]
    · intro hc
      apply hne
      ext i
      have hh := congrFun hc i
      exact Complex.ofReal_injective (by simpa using hh)
  let e := LinearEquiv.ofInjectiveEndo ((LinearMap.id : Module.End ℝ (Fin n → ℝ)) - B) hinj
  exact ⟨e.toContinuousLinearEquiv, fun v ↦ rfl⟩


end HolomorphicAnosov.Topology
