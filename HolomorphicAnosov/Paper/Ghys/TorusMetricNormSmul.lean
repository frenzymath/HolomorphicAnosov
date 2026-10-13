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
import HolomorphicAnosov.Paper.Ghys.TorusMetricNorm

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology Manifold Bundle
open IsManifold
attribute [local instance] complexTorus_isManifold complex_isManifold_real
set_option backward.isDefEq.respectTransparency false

theorem torus_metric_norm_smul {d : ℕ} (L : FullComplexLattice d)
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : ComplexTorus L ↦ TangentSpace (realModel d) x))
    (x : ComplexTorus L) (r : ℝ) (v : ComplexModel d) :
    torusMetricNorm L g x (r • v) = |r| * torusMetricNorm L g x v := by
  unfold torusMetricNorm
  have heq : g.inner x (r • v) (r • v) = r ^ 2 * g.inner x v v := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [heq, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

end HolomorphicAnosov
