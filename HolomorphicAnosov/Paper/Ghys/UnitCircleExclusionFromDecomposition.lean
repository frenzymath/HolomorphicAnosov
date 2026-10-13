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

theorem unit_circle_exclusion_from_decomposition
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A : V →ₗ[ℂ] V) (μ : ℂ) (v s u : V) (C lam : ℝ)
    (hv : Module.End.HasEigenvector A μ v) (hμ : ‖μ‖ = 1)
    (hC : 0 ≤ C) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hvs : v = s + u)
    (hs : ∀ n : ℕ, ‖(A ^ n) s‖ ≤ C * lam ^ n * ‖s‖)
    (hu : ∀ n : ℕ, ‖u‖ ≤ C * lam ^ n * ‖(A ^ n) u‖) : False := by
  have hvn (n : ℕ) : ‖(A ^ n) v‖ = ‖v‖ := by
    rw [hv.pow_apply, norm_smul, norm_pow, hμ, one_pow, one_mul]
  have hun (n : ℕ) : ‖(A ^ n) u‖ ≤ ‖v‖ + C * ‖s‖ := by
    have he : (A ^ n) u = (A ^ n) v - (A ^ n) s := by
      rw [hvs, map_add, add_sub_cancel_left]
    rw [he]
    calc
      ‖(A ^ n) v - (A ^ n) s‖ ≤ ‖(A ^ n) v‖ + ‖(A ^ n) s‖ := norm_sub_le _ _
      _ ≤ ‖v‖ + C * lam ^ n * ‖s‖ := by rw [hvn]; exact add_le_add_right (hs n) _
      _ ≤ ‖v‖ + C * ‖s‖ := by
        apply add_le_add_right
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg s)
        simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hlam0 hlam1.le (n := n)) hC
  have ht : Filter.Tendsto (fun n : ℕ ↦ C * lam ^ n * (‖v‖ + C * ‖s‖))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0 hlam1)).mul_const (‖v‖ + C * ‖s‖)
  have hu0 : u = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    exact ge_of_tendsto ht (Filter.Eventually.of_forall (fun n ↦
      (hu n).trans (mul_le_mul_of_nonneg_left (hun n)
        (mul_nonneg hC (pow_nonneg hlam0 n)))))
  have hsv : s = v := by simpa [hu0] using hvs.symm
  have ht' : Filter.Tendsto (fun n : ℕ ↦ C * lam ^ n * ‖s‖)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0 hlam1)).mul_const ‖s‖
  have hv0 : v = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    exact ge_of_tendsto ht' (Filter.Eventually.of_forall (fun n ↦ by
      simpa only [hsv, hvn] using hs n))
  exact hv.2 hv0

end HolomorphicAnosov
