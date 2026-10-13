import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexTestFromEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexTestFromEuclideanApply
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomain
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordPullbackCLM
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.OrderedEuclideanIntegrableOnTransport
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.OrderedEuclideanOpenIntegralTransport
import HolomorphicAnosov.Analysis.DistributionSmoothFixedSupportFamily
import Mathlib.Analysis.Distribution.TestFunction

/-!
# complex_fixed_support_pairing

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.E (3.29),
pp.28–29, separated cutoff kernel and regularization; fixed-support pairing follows Dyatlov
Proposition6.3, pp.68–69, and Lemma6.8/Remark6.9, pp.72–73.
DAG node: `analysis.dbar_helper_complex_fixed_support_pairing_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
A jointly smooth Euclidean-coordinate kernel with one compact spatial support gives test sections
in the original complex domains, a smooth paired function, and an integrated test whose current
pairing exchanges with parameter integration.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.E (3.29),
pp.28–29, separated cutoff kernel and regularization; fixed-support pairing follows Dyatlov
Proposition6.3, pp.68–69, and Lemma6.8/Remark6.9, pp.72–73.

Proof/construction: Apply the existing fixed-support family theorem to the transported
distribution and inverse-coordinate parameter domain. Pull its sections back to complex
coordinates; smoothness follows by composition with the coordinate equivalence. Pull each
parameter test in the opposite direction, apply the provider integral identity, and use volume
transport for every integral and its integrability guard. Test support is the preimage of the
fixed compact support.
-/
theorem complex_fixed_support_pairing {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (U : Opens (Fin n → ℂ)) (P : Opens (Fin k → ℂ))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (K : Set (EuclideanSpace ℝ (Fin (n+n)))) (hK : IsCompact K)
    (hKU : K ⊆ coordDomain (complexToOrderedEuclidean n).symm U)
    (H : EuclideanSpace ℝ (Fin (k+k)) → EuclideanSpace ℝ (Fin (n+n)) → ℂ)
    (hH : ContDiffOn ℝ ∞ (Function.uncurry H)
      ((coordDomain (complexToOrderedEuclidean k).symm P : Set _) ×ˢ
        (coordDomain (complexToOrderedEuclidean n).symm U : Set _)))
    (hSupport : ∀ p ∈ coordDomain (complexToOrderedEuclidean k).symm P,
      tsupport (H p) ⊆ K) :
    ∃ sections : (Fin k → ℂ) → TestFunction U ℂ ⊤,
      (∀ p ∈ P, ∀ y, sections p y =
        H (complexToOrderedEuclidean k p) (complexToOrderedEuclidean n y)) ∧
      ContDiffOn ℝ ∞ (fun p ↦ T (sections p)) (P : Set _) ∧
      (∀ φ : TestFunction P ℂ ⊤, ∃ η : TestFunction U ℂ ⊤,
        (∀ y, IntegrableOn (fun p ↦ φ p *
          H (complexToOrderedEuclidean k p) (complexToOrderedEuclidean n y))
          (P : Set _) volume) ∧
        (∀ y, η y = ∫ p in (P : Set _), φ p *
          H (complexToOrderedEuclidean k p) (complexToOrderedEuclidean n y)) ∧
        tsupport (η : (Fin n → ℂ) → ℂ) ⊆ (complexToOrderedEuclidean n) ⁻¹' K ∧
        IntegrableOn (fun p ↦ φ p * T (sections p)) (P : Set _) volume ∧
        T η = ∫ p in (P : Set _), φ p * T (sections p)) := by
  let W := coordDomain (complexToOrderedEuclidean n).symm U
  let Q := coordDomain (complexToOrderedEuclidean k).symm P
  let S := T.comp (complexTestFromEuclidean U)
  obtain ⟨s, hs, hsm, _, hi⟩ := distribution_smooth_fixed_support_family
    (show 0 < n+n by omega) (show 0 < k+k by omega) W Q S K hK hKU H hH hSupport
  let sections : (Fin k → ℂ) → TestFunction U ℂ ⊤ := fun p ↦
    complexTestFromEuclidean U (s (complexToOrderedEuclidean k p))
  have hmem (p : Fin k → ℂ) (hp : p ∈ P) : complexToOrderedEuclidean k p ∈ Q := by
    change (complexToOrderedEuclidean k).symm (complexToOrderedEuclidean k p) ∈ P
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hp
  refine ⟨sections, ?_, ?_, ?_⟩
  · intro p hp y
    rw [complexTestFromEuclidean_apply]
    exact hs _ (hmem p hp) _
  · exact hsm.comp (complexToOrderedEuclidean k).contDiff.contDiffOn hmem
  · intro φ
    let φQ := coordPullbackCLM (complexToOrderedEuclidean k).symm P φ
    have hφQ (p : Fin k → ℂ) : φQ (complexToOrderedEuclidean k p) = φ p := by
      change φ ((complexToOrderedEuclidean k).symm (complexToOrderedEuclidean k p)) = _
      rw [ContinuousLinearEquiv.symm_apply_apply]
    obtain ⟨η, hint, hη, hsupp, hintpair, hpair⟩ := hi φQ
    refine ⟨complexTestFromEuclidean U η, ?_, ?_, ?_, ?_, ?_⟩
    · intro y
      have hh := (ordered_euclidean_integrableOn_transport P
        (fun p ↦ φQ p * H p (complexToOrderedEuclidean n y))).mp
        (hint (complexToOrderedEuclidean n y))
      simpa only [hφQ] using hh
    · intro y
      rw [complexTestFromEuclidean_apply, hη,
        ordered_euclidean_open_integral_transport P]
      simp only [hφQ]
    · have heq : (complexTestFromEuclidean U η : (Fin n → ℂ) → ℂ) =
          (η : EuclideanSpace ℝ (Fin (n+n)) → ℂ) ∘ complexToOrderedEuclidean n := by
        funext y
        exact complexTestFromEuclidean_apply U η y
      rw [heq]
      exact (tsupport_comp_subset_preimage η (complexToOrderedEuclidean n).continuous).trans
        (preimage_mono hsupp)
    · have hh := (ordered_euclidean_integrableOn_transport P
        (fun p ↦ φQ p * S (s p))).mp hintpair
      simpa only [hφQ, S, sections, ContinuousLinearMap.comp_apply] using hh
    · change S η = _
      rw [hpair, ordered_euclidean_open_integral_transport P]
      simp only [hφQ]
      rfl


end HolomorphicAnosov.Analysis.Distribution
