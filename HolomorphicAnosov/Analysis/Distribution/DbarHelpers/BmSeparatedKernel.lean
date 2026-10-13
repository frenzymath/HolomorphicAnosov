import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliCompactSupport

/-!
# bmSeparatedKernel

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.D (3.23), p.26, and §3.E (3.29), p.28, scalar cutoff kernel.
DAG node: `analysis.dbar_helper_bm_separated_kernel_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/--
Given a family of scalar coefficient functions indexed by Fin n, the separated scalar
Bochner–Martinelli kernel is minus (n-1)! divided by pi^n times the sum of the scalar kernel
coefficients multiplied by those functions in the spatial variable.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.D (3.23), p.26, and §3.E (3.29), p.28, scalar cutoff kernel.

Proof/construction: Use the scalar coefficients of the published Bochner–Martinelli kernel and the
finite coordinate sum with the source scalar normalization. The intended coefficients are the
antiholomorphic derivatives of a cutoff.
-/
noncomputable def bmSeparatedKernel {n : ℕ} (a : Fin n → (Fin n → ℂ) → ℂ)
    (z w : Fin n → ℂ) : ℂ :=
  -((Nat.factorial (n - 1) : ℂ) / (Real.pi : ℂ) ^ n) *
    ∑ j, scalarBochnerMartinelliKernel j z w * a j w


end HolomorphicAnosov.Analysis
