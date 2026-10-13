import HolomorphicAnosov.Paper.Ghys.QuotientAffineEquiv
import HolomorphicAnosov.Dynamics.Anosov.IterateInvariant
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
import HolomorphicAnosov.Paper.Ghys.TorusCompactComplexManifold
import HolomorphicAnosov.Paper.Ghys.TorusMetricComparison
import HolomorphicAnosov.Paper.Ghys.AffineIterateDerivative
import HolomorphicAnosov.Paper.Ghys.TorusInverseIterateDerivative
import HolomorphicAnosov.Paper.Ghys.UnitCircleExclusionFromDecomposition

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology Manifold Bundle
open IsManifold
attribute [local instance] complexTorus_isManifold complex_isManifold_real
set_option backward.isDefEq.respectTransparency false

theorem affine_anosov_hyperbolic {d : ℕ} (L : FullComplexLattice d)
    (A : LatticeLinearEquiv L) (b : ComplexModel d)
    (f : Biholomorph d d (ComplexTorus L) (ComplexTorus L))
    (hf : ∀ x, f x = quotientAffineEquiv A b x) (a : AnosovDatum f) :
    ∀ μ : ℂ, Module.End.HasEigenvalue A.linear.toLinearMap μ → ‖μ‖ ≠ 1 := by
  let := torus_compact_complex_manifold L
  obtain ⟨m, M, hm, hM, hmetric⟩ := torus_metric_comparison L a.metric
  obtain ⟨C, lam, hC, hlam, hlam1, hs, hu⟩ := fixed_block_uniform_anosov_estimates f a
  intro μ hμ hnorm
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  let x : ComplexTorus L := 0
  obtain ⟨s, u, hsu, _⟩ := Submodule.existsUnique_add_of_isCompl (a.splitting.isCompl x) v
  let sv : ComplexModel d := s.val
  let uv : ComplexModel d := u.val
  have hstable : ∀ n, ‖(A.linear.toLinearMap ^ n) sv‖ ≤
      (C * M / m) * lam ^ n * ‖sv‖ := by
    intro n
    have h := hs n x s.val s.property
    change torusMetricNorm L a.metric (((f : ComplexTorus L → ComplexTorus L)^[n]) x)
      (mfderiv (realModel d) (realModel d) ((f : ComplexTorus L → ComplexTorus L)^[n]) x sv) ≤
      C * lam ^ n * torusMetricNorm L a.metric x sv at h
    erw [affine_iterate_derivative A b f hf] at h
    have hleft := (hmetric (((f : ComplexTorus L → ComplexTorus L)^[n]) x)
      ((A.linear.toLinearMap ^ n) sv)).1
    have hright := mul_le_mul_of_nonneg_left (hmetric x sv).2
      (mul_nonneg hC.le (pow_nonneg hlam.le n))
    have ht : m * ‖(A.linear.toLinearMap ^ n) sv‖ ≤
        C * lam ^ n * (M * ‖sv‖) := hleft.trans (h.trans hright)
    have ht' := (le_div_iff₀ hm).mpr (by simpa only [mul_comm] using ht)
    convert ht' using 1; ring
  have hunstable : ∀ n, ‖uv‖ ≤ (C * M / m) * lam ^ n *
      ‖(A.linear.toLinearMap ^ n) uv‖ := by
    intro n
    let y := ((f : ComplexTorus L → ComplexTorus L)^[n]) x
    let w := mfderiv (realModel d) (realModel d)
      ((f : ComplexTorus L → ComplexTorus L)^[n]) x u.val
    have hw : w ∈ a.splitting.unstable.toDistribution y := by
      have hi := real_distribution_iterate_invariant f.toReal
        a.splitting.unstable.toDistribution a.splitting.unstable_map n x
      change w ∈ a.splitting.unstable.toDistribution ((f.toReal : ComplexTorus L → ComplexTorus L)^[n] x)
      rw [← hi]
      exact ⟨u.val, u.property, rfl⟩
    have h := hu n y w hw
    change torusMetricNorm L a.metric (((f.symm : ComplexTorus L → ComplexTorus L)^[n]) y)
      (mfderiv (realModel d) (realModel d) ((f.symm : ComplexTorus L → ComplexTorus L)^[n]) y w) ≤
      C * lam ^ n * torusMetricNorm L a.metric y w at h
    have hinv : ((f.symm : ComplexTorus L → ComplexTorus L)^[n]) y = x :=
      (realIterate (realModel d) f.toReal n).symm_apply_apply x
    rw [hinv] at h
    erw [torus_inverse_iterate_derivative f n x uv] at h
    dsimp only [w] at h
    erw [affine_iterate_derivative A b f hf] at h
    have ht := (hmetric x uv).1.trans (h.trans
      (mul_le_mul_of_nonneg_left (hmetric y ((A.linear.toLinearMap ^ n) uv)).2
        (mul_nonneg hC.le (pow_nonneg hlam.le n))))
    have ht' := (le_div_iff₀ hm).mpr (by simpa only [mul_comm] using ht)
    convert ht' using 1; ring
  exact unit_circle_exclusion_from_decomposition A.linear.toLinearMap μ v sv uv
    (C * M / m) lam hv hnorm (div_nonneg (mul_nonneg hC.le hM.le) hm.le)
    hlam.le hlam1 hsu.symm hstable hunstable

end HolomorphicAnosov
