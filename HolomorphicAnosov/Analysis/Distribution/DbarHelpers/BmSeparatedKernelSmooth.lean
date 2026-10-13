import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.BmSeparatedKernel
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.BmKernelSmoothOffDiagonal

/-!
# BmSeparatedKernelSmooth

Source: Demailly, Complex Analytic and Differential Geometry (2012), I §3.E (3.29), pp.28–29,
smooth cutoff term supported away from the diagonal; I (3.26), p.27, absence of off-diagonal
singularities.
DAG node: `analysis.dbar_helper_bm_separated_kernel_smooth_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/--
If each coefficient of a finite scalar Bochner–Martinelli kernel is globally smooth and its closed
support avoids a parameter set P, the coefficient-weighted kernel is jointly smooth on P times the
whole spatial space.

Source: Demailly (2012), I §3.E (3.29), pp.28–29, smooth cutoff term supported away from the
diagonal; I (3.26), p.27, absence of off-diagonal singularities.

Proof: Consider each summand of the displayed cutoff kernel. Off the diagonal the scalar kernel is
smooth and so is its coefficient. At a diagonal point belonging to P, the coefficient vanishes on
a spatial neighborhood by its support separation. The summand is consequently zero on a product
neighborhood and hence smooth there. Multiply by the constant normalization and sum the finitely
many smooth summands.
-/
theorem bm_separated_kernel_smooth {n : ℕ} (P : Set (Fin n → ℂ))
    (a : Fin n → (Fin n → ℂ) → ℂ) (ha : ∀ j, ContDiff ℝ ∞ (a j))
    (hsep : ∀ j z, z ∈ P → z ∉ tsupport (a j)) :
    ContDiffOn ℝ ∞ (Function.uncurry (bmSeparatedKernel a)) (P ×ˢ Set.univ) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro j _
  by_cases h : p.2 = p.1
  · have hz : a j =ᶠ[𝓝 p.2] (fun _ ↦ (0 : ℂ)) :=
      (notMem_tsupport_iff_eventuallyEq.mp (h ▸ hsep j p.1 hp.1))
    have hz' := continuousAt_snd.eventually hz
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hz'] with q hq
    simp only [hq, mul_zero]
  · exact (bm_kernel_smooth_off_diagonal j p.1 p.2 h).mul
      ((ha j).comp contDiff_snd).contDiffAt


end HolomorphicAnosov.Analysis
