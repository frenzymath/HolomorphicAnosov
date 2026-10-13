import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.BmSeparatedKernel
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CutoffBmKernelFamily
import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliCompactSupport
import Mathlib.Analysis.Distribution.TestFunction

/-!
# cutoff_bm_kernel_euclidean

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.E (3.29),
pp.28–29, separated cutoff kernel and regularization; fixed-support pairing follows Dyatlov
Proposition6.3, pp.68–69, and Lemma6.8/Remark6.9, pp.72–73.
DAG node: `analysis.dbar_helper_cutoff_bm_kernel_euclidean_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/--
Under a real continuous linear coordinate equivalence, the cutoff-derived kernel satisfies the
Euclidean fixed-support family hypotheses.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.E (3.29),
pp.28–29, separated cutoff kernel and regularization; fixed-support pairing follows Dyatlov
Proposition6.3, pp.68–69, and Lemma6.8/Remark6.9, pp.72–73.

Proof/construction: Compose joint smoothness with the inverse linear map in both variables. The
image of the compact cutoff support is compact and lies in the inverse-coordinate open domain by
cancellation of the equivalence. Support of composition lies in the inverse-map preimage, which is
the forward image of the old support.
-/
theorem cutoff_bm_kernel_euclidean {n : ℕ}
    (e : (Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n+n)))
    (U P : Opens (Fin n → ℂ)) (ψ : TestFunction U ℂ ⊤)
    (hψ : ∀ z ∈ P, ψ z = 1) :
    let H := fun p y ↦ bmSeparatedKernel (fun j ↦ antiholomorphicPartial ψ j)
      (e.symm p) (e.symm y)
    let K := e '' tsupport (ψ : (Fin n → ℂ) → ℂ)
    ContDiffOn ℝ ∞ (Function.uncurry H)
      ((e.symm ⁻¹' (P : Set _)) ×ˢ (e.symm ⁻¹' (U : Set _))) ∧
      IsCompact K ∧ K ⊆ e.symm ⁻¹' (U : Set _) ∧
      (∀ p, tsupport (H p) ⊆ K) := by
  dsimp only
  obtain ⟨hsmooth, hcompact, hsupp⟩ := cutoff_bm_kernel_family U ψ P P.isOpen hψ
  refine ⟨?_, hcompact.image e.continuous, ?_, ?_⟩
  · have hcoord : ContDiff ℝ ∞ (fun q :
        EuclideanSpace ℝ (Fin (n+n)) × EuclideanSpace ℝ (Fin (n+n)) ↦
        (e.symm q.1, e.symm q.2)) :=
        (e.symm.contDiff.comp contDiff_fst).prodMk
          (e.symm.contDiff.comp contDiff_snd)
    have hc := hsmooth.comp (s :=
      ((e.symm ⁻¹' (P : Set _)) ×ˢ (e.symm ⁻¹' (U : Set _))))
      hcoord.contDiffOn (fun p hp ↦ ⟨hp.1, Set.mem_univ _⟩)
    exact hc
  · rintro _ ⟨x, hx, rfl⟩
    change e.symm (e x) ∈ U
    rw [e.symm_apply_apply]
    exact ψ.tsupport_subset hx
  · intro p
    refine (tsupport_comp_subset_preimage
      (bmSeparatedKernel (fun j ↦ antiholomorphicPartial ψ j) (e.symm p))
      e.symm.continuous).trans ?_
    intro y hy
    exact ⟨e.symm y, hsupp _ hy, e.apply_symm_apply y⟩


end HolomorphicAnosov.Analysis
