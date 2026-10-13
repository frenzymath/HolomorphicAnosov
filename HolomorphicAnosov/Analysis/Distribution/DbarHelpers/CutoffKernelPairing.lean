import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.BmSeparatedKernel
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexFixedSupportPairing
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CutoffBmKernelEuclidean
import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliCompactSupport
import Mathlib.Analysis.Distribution.TestFunction

/-!
# cutoff_kernel_pairing

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.E (3.29),
pp.28–29, separated cutoff kernel and regularization; fixed-support pairing follows Dyatlov
Proposition6.3, pp.68–69, and Lemma6.8/Remark6.9, pp.72–73.
DAG node: `analysis.dbar_helper_cutoff_kernel_pairing_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
Pairing a scalar current with the actual separated cutoff kernel gives smooth test sections and
the fixed-support parameter integration identity on the original complex domains.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.E (3.29),
pp.28–29, separated cutoff kernel and regularization; fixed-support pairing follows Dyatlov
Proposition6.3, pp.68–69, and Lemma6.8/Remark6.9, pp.72–73.

Proof/construction: Apply the kernel-coordinate smoothness and common-support theorem using the
ordered coordinate equivalence. Feed these guards into the complex-coordinate fixed-support
pairing provider, and simplify the two inverse-coordinate compositions. This is the paired cutoff
term in Demailly’s formula.
-/
theorem cutoff_kernel_pairing {n : ℕ} (hn : 1 ≤ n)
    (U P : Opens (Fin n → ℂ)) (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (ψ : TestFunction U ℂ ⊤) (hψ : ∀ z ∈ P, ψ z = 1) :
    let H := bmSeparatedKernel (fun j ↦ antiholomorphicPartial ψ j)
    ∃ sections : (Fin n → ℂ) → TestFunction U ℂ ⊤,
      (∀ p ∈ P, ∀ y, sections p y = H p y) ∧
      ContDiffOn ℝ ∞ (fun p ↦ T (sections p)) (P : Set _) ∧
      (∀ φ : TestFunction P ℂ ⊤, ∃ η : TestFunction U ℂ ⊤,
        (∀ y, IntegrableOn (fun p ↦ φ p * H p y) (P : Set _) volume) ∧
        (∀ y, η y = ∫ p in (P : Set _), φ p * H p y) ∧
        tsupport (η : (Fin n → ℂ) → ℂ) ⊆ tsupport (ψ : (Fin n → ℂ) → ℂ) ∧
        IntegrableOn (fun p ↦ φ p * T (sections p)) (P : Set _) volume ∧
        T η = ∫ p in (P : Set _), φ p * T (sections p)) := by
  dsimp only
  let e := complexToOrderedEuclidean n
  let H := bmSeparatedKernel (fun j ↦ antiholomorphicPartial ψ j)
  obtain ⟨hH, hK, hKU, hsupport⟩ := cutoff_bm_kernel_euclidean e U P ψ hψ
  obtain ⟨s, hs, hsm, hi⟩ := complex_fixed_support_pairing hn hn U P T
    (e '' tsupport (ψ : (Fin n → ℂ) → ℂ)) hK hKU
    (fun p y ↦ H (e.symm p) (e.symm y)) hH (fun p _ ↦ hsupport p)
  refine ⟨s, ?_, hsm, ?_⟩
  · intro p hp y
    simpa only [e, H, ContinuousLinearEquiv.symm_apply_apply] using hs p hp y
  · intro φ
    obtain ⟨η, hint, hη, hsupp, hintpair, hpair⟩ := hi φ
    refine ⟨η, ?_, ?_, ?_, hintpair, hpair⟩
    · intro y
      simpa only [e, H, ContinuousLinearEquiv.symm_apply_apply] using hint y
    · intro y
      simpa only [e, H, ContinuousLinearEquiv.symm_apply_apply] using hη y
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hsupp hy
      exact e.injective hxy ▸ hx


end HolomorphicAnosov.Analysis.Distribution
