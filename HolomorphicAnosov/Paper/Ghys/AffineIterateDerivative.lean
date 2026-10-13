import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LatticeLinearEquiv
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import Mathlib.Algebra.Group.Units.Equiv
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Charts
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LinearMap
import HolomorphicAnosov.Paper.Zhang.Anosov
import Mathlib.LinearAlgebra.Eigenspace.Basic
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic
import HolomorphicAnosov.Paper.Ghys.AffineDerivative

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology Manifold Bundle
open IsManifold
attribute [local instance] complexTorus_isManifold complex_isManifold_real
set_option backward.isDefEq.respectTransparency false

theorem affine_iterate_derivative {d : ℕ} {L : FullComplexLattice d}
    (A : LatticeLinearEquiv L) (b : ComplexModel d)
    (f : Biholomorph d d (ComplexTorus L) (ComplexTorus L))
    (hf : ∀ x, f x = quotientAffineEquiv A b x) (n : ℕ) (x : ComplexTorus L)
    (v : ComplexModel d) :
    mfderiv (realModel d) (realModel d) ((f : ComplexTorus L → ComplexTorus L)^[n]) x v =
      (A.linear.toLinearMap ^ n) v := by
  induction n generalizing x v with
  | zero =>
    simp only [Function.iterate_zero, mfderiv_id, pow_zero, Module.End.one_apply]
    rfl
  | succ n ih =>
    rw [Function.iterate_succ]
    erw [mfderiv_comp x ((f.toReal.contMDiff.iterate n).mdifferentiableAt (by simp))
      (f.toReal.contMDiff.mdifferentiableAt (by simp))]
    erw [ContinuousLinearMap.comp_apply]
    erw [ih]
    erw [affine_derivative A b f hf]
    change (A.linear.toLinearMap ^ n) (A.linear v) = (A.linear.toLinearMap ^ (n+1)) v
    rw [pow_succ]
    rfl

end HolomorphicAnosov
