import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.BmSeparatedKernel
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CutoffBmKernelFamily
import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliCompactSupport
import Mathlib.Analysis.Distribution.TestFunction

/-!
# cutoff_kernel_product_integrable

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.E (3.29),
pp.28–29, separated cutoff kernel and regularization; fixed-support pairing follows Dyatlov
Proposition6.3, pp.68–69, and Lemma6.8/Remark6.9, pp.72–73.
DAG node: `analysis.dbar_helper_cutoff_kernel_product_integrable_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
The product of a parameter test, the separated cutoff kernel and a coefficient continuous on the
cutoff support is integrable for the product of two restricted volume measures.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.E (3.29),
pp.28–29, separated cutoff kernel and regularization; fixed-support pairing follows Dyatlov
Proposition6.3, pp.68–69, and Lemma6.8/Remark6.9, pp.72–73.

Proof/construction: The product vanishes outside the product of the parameter-test support and the
cutoff support. That set is compact. On it, the test and kernel are continuous and the coefficient
is continuous by hypothesis. Native compact-support integrability supplies the Fubini guard,
without any regularity premise outside that compact set.
-/
theorem cutoff_kernel_product_integrable {n : ℕ}
    (U P Q : Opens (Fin n → ℂ)) (ψ : TestFunction U ℂ ⊤)
    (hψ : ∀ z ∈ P, ψ z = 1) (φ : TestFunction P ℂ ⊤)
    (f : (Fin n → ℂ) → ℂ)
    (hf : ContinuousOn f (tsupport (ψ : (Fin n → ℂ) → ℂ))) :
    Integrable (fun q : (Fin n → ℂ) × (Fin n → ℂ) ↦
      φ q.1 * bmSeparatedKernel (fun j ↦ antiholomorphicPartial ψ j) q.1 q.2 * f q.2)
      ((volume.restrict (P : Set _)).prod (volume.restrict (Q : Set _))) := by
  let H := bmSeparatedKernel (fun j ↦ antiholomorphicPartial ψ j)
  let K := tsupport (φ : (Fin n → ℂ) → ℂ) ×ˢ tsupport (ψ : (Fin n → ℂ) → ℂ)
  obtain ⟨hH, _, hsupp⟩ := cutoff_bm_kernel_family U ψ P P.isOpen hψ
  have hsupport : Function.support (fun q : (Fin n → ℂ) × (Fin n → ℂ) ↦
      φ q.1 * H q.1 q.2 * f q.2) ⊆ K := by
    intro q hq
    constructor
    · apply subset_tsupport φ
      intro hzero
      exact hq (by simp [hzero])
    · apply hsupp q.1
      apply subset_tsupport (H q.1)
      intro hzero
      exact hq (by simp [hzero])
  apply (integrableOn_iff_integrable_of_support_subset hsupport).mp
  apply ContinuousOn.integrableOn_compact
    (φ.hasCompactSupport.prod ψ.hasCompactSupport)
  have hprod : K ⊆ (P : Set _) ×ˢ (Set.univ : Set (Fin n → ℂ)) :=
    fun q hq ↦ ⟨φ.tsupport_subset hq.1, Set.mem_univ _⟩
  exact ((φ.contDiff.continuous.comp continuous_fst).continuousOn.mul
    (hH.continuousOn.mono hprod)).mul
      (hf.comp continuous_snd.continuousOn (fun _ hq ↦ hq.2))


end HolomorphicAnosov.Analysis.Distribution
