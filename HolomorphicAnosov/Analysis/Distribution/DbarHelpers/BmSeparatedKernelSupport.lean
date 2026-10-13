import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.BmSeparatedKernel

/-!
# BmSeparatedKernelSupport

Source: Demailly, Complex Analytic and Differential Geometry (2012), I §3.E (3.29), p.28, the
spatial support of the displayed coefficient-weighted cutoff kernel.
DAG node: `analysis.dbar_helper_bm_separated_kernel_support_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/--
If all coefficient functions in the scalar Bochner–Martinelli kernel are supported in one closed
set K, every spatial section of the weighted kernel has closed support in K.

Source: Demailly (2012), I §3.E (3.29), p.28, the spatial support of the displayed
coefficient-weighted cutoff kernel.

Proof: At a point outside K each coefficient vanishes, because its closed support lies in K. Every
summand in the displayed finite kernel sum is therefore zero, so the kernel section itself
vanishes there. Its nonzero set is contained in K; taking the closure preserves this inclusion
because K is closed.
-/
theorem bm_separated_kernel_support {n : ℕ} (a : Fin n → (Fin n → ℂ) → ℂ)
    (K : Set (Fin n → ℂ)) (hK : IsClosed K) (ha : ∀ j, tsupport (a j) ⊆ K)
    (z : Fin n → ℂ) : tsupport (bmSeparatedKernel a z) ⊆ K := by
  apply closure_minimal _ hK
  intro w hw
  by_contra hnot
  have hzero (j : Fin n) : a j w = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hmem ↦ hnot (ha j hmem))
  exact hw (by simp [bmSeparatedKernel, hzero])


end HolomorphicAnosov.Analysis
