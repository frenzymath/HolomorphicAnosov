import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.BmSeparatedKernel
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.BmSeparatedKernelSmooth
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.BmSeparatedKernelSupport
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CutoffDbarSmoothSupport
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CutoffDbarSupportSeparated
import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliCompactSupport
import Mathlib.Analysis.Distribution.TestFunction

/-!
# cutoff_bm_kernel_family

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.E (3.29),
pp.28–29, separated cutoff kernel and regularization; fixed-support pairing follows Dyatlov
Proposition6.3, pp.68–69, and Lemma6.8/Remark6.9, pp.72–73.
DAG node: `analysis.dbar_helper_cutoff_bm_kernel_family_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/--
The actual cutoff-derived scalar Bochner–Martinelli kernel is jointly smooth on an open region
where the cutoff is one and has a common compact spatial support.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.E (3.29),
pp.28–29, separated cutoff kernel and regularization; fixed-support pairing follows Dyatlov
Proposition6.3, pp.68–69, and Lemma6.8/Remark6.9, pp.72–73.

Proof/construction: Its coefficient derivatives are smooth and supported in the cutoff support.
They vanish on a neighborhood of the parameter region, so the separated-kernel smoothness theorem
applies. The cutoff support is compact, and the separated-kernel support theorem confines every
section to it.
-/
theorem cutoff_bm_kernel_family {n : ℕ} (U : Opens (Fin n → ℂ))
    (ψ : TestFunction U ℂ ⊤) (O : Set (Fin n → ℂ)) (hO : IsOpen O)
    (hψ : ∀ z ∈ O, ψ z = 1) :
    let H := bmSeparatedKernel (fun j ↦ antiholomorphicPartial ψ j)
    ContDiffOn ℝ ∞ (Function.uncurry H) (O ×ˢ Set.univ) ∧
      IsCompact (tsupport (ψ : (Fin n → ℂ) → ℂ)) ∧
      (∀ z, tsupport (H z) ⊆ tsupport (ψ : (Fin n → ℂ) → ℂ)) := by
  refine ⟨bm_separated_kernel_smooth O _
    (fun j ↦ (cutoff_dbar_smooth_support U ψ j).1)
    (cutoff_dbar_support_separated ψ O hO hψ), ψ.hasCompactSupport, ?_⟩
  exact bm_separated_kernel_support _ _ (isClosed_tsupport _)
    (fun j ↦ (cutoff_dbar_smooth_support U ψ j).2)


end HolomorphicAnosov.Analysis
