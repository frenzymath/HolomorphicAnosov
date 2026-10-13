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

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology Manifold Bundle
open IsManifold
attribute [local instance] complexTorus_isManifold complex_isManifold_real
set_option backward.isDefEq.respectTransparency false

theorem torus_inverse_iterate_derivative {d : ℕ} {L : FullComplexLattice d}
    (f : Biholomorph d d (ComplexTorus L) (ComplexTorus L)) (n : ℕ)
    (x : ComplexTorus L) (v : ComplexModel d) :
    mfderiv (realModel d) (realModel d) ((f.symm : ComplexTorus L → ComplexTorus L)^[n])
      ((f : ComplexTorus L → ComplexTorus L)^[n] x)
      (mfderiv (realModel d) (realModel d) ((f : ComplexTorus L → ComplexTorus L)^[n]) x v) = v := by
  let g := realIterate (realModel d) f.toReal n
  have hc : (g.symm : ComplexTorus L → ComplexTorus L) ∘ g = id := by
    funext y
    exact g.symm_apply_apply y
  have hd := mfderiv_comp x (g.symm.contMDiff.mdifferentiableAt (by simp))
    (g.contMDiff.mdifferentiableAt (by simp))
  rw [hc, mfderiv_id, g.symm_apply_apply] at hd
  exact (congrArg (fun L ↦ L v) hd).symm

end HolomorphicAnosov
