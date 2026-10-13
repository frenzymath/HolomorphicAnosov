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
import HolomorphicAnosov.Paper.Ghys.TorusFlatFrameContinuous

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology Manifold Bundle
open IsManifold
attribute [local instance] complexTorus_isManifold complex_isManifold_real
set_option backward.isDefEq.respectTransparency false

theorem torus_metric_norm_continuous {d : ℕ} (L : FullComplexLattice d)
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : ComplexTorus L ↦ TangentSpace (realModel d) x)) :
    Continuous (fun p : ComplexTorus L × ComplexModel d ↦ torusMetricNorm L g p.1 p.2) := by
  have h := torus_flat_frame_continuous L
  have hg := (g.contMDiff.continuous.comp continuous_fst).clm_bundle_apply₂
    (𝕜 := ℝ) (F₁ := ComplexModel d) (F₂ := ComplexModel d) (F₃ := ℝ)
    (E₃ := Bundle.Trivial (ComplexTorus L) ℝ) (ψ := fun p ↦ g.inner p.1) h h
  exact ((Bundle.Trivial.homeomorphProd (ComplexTorus L) ℝ).continuous.comp hg).snd.sqrt

end HolomorphicAnosov
