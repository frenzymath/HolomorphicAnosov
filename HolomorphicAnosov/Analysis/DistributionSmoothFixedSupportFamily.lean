import HolomorphicAnosov.Analysis.TestFunctionFixedSupport
import HolomorphicAnosov.Analysis.Distribution.FixedSupportSmoothPairing
import HolomorphicAnosov.Analysis.Distribution.FixedSupportIntegralPairing

/-!
# Distributions on smooth families with fixed compact support

This module states `analysis.distribution_smooth_fixed_support_family_g2`.
Source: S. Dyatlov, *Lecture notes for 18.155: distributions, elliptic regularity,
and applications to PDEs*, 2 October 2026, Proposition 6.3, pp. 68–69, and
Lemma 6.8 with Remark 6.9, pp. 71–73; test functions and the unconjugated
complex-linear pairing are defined in §§1.2 and 2, pp. 13–14 and 27–30.

`TestFunction` carries Mathlib's canonical locally convex LF topology. The
distribution below is literally a continuous complex-linear functional on
complex-valued tests; no identification with Mathlib's real-test `Distribution`
abbreviation is used. Tests are smooth zero extensions on the ambient real
Euclidean space, with compact topological support contained in the open set.

The ambient function `H` is a total representative of the function on `P × U`.
The fixed-support hypothesis makes it zero outside `K` for parameters in `P`.
Its arbitrary values outside `P` have no effect: all parameter derivatives are
within the open set `P`, and both integrals are restricted to `P`.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace HolomorphicAnosov.Analysis

/-- A continuous complex-linear distribution pairs smoothly with a jointly
smooth family of tests supported in one compact set, commutes with every real
parameter multi-index derivative, and commutes with compactly supported
parameter integration. Multiplication and pairing have no complex conjugation.

The multi-index `α : Fin k → ℕ` is represented by the list of standard real
coordinate vectors containing `α i` copies of the `i`-th vector, in coordinate
order. Evaluating the iterated real Fréchet derivative on that list is precisely
`∂ᵅ`. The empty list includes the order-zero formula. Joint smoothness makes
these mixed partials independent of the chosen ordering.

Proof from Dyatlov Proposition 6.3, pp. 68–69, and Lemma 6.8 / Remark 6.9,
pp. 71–73, with the source's proper-support alternative specialized to `K`:
on each compact parameter ball all sections and their derivatives have support
in `K`. Smoothness on `U` and the compact containment `K ⊆ U` give smooth zero
extensions, hence actual `TestFunction` sections. Continuity of `T` on the LF
space yields a finite-order bound on the fixed-support space: otherwise choose
tests with pairing one and derivative seminorms through order `j` less than
`1/j`, contradicting continuity of the canonical fixed-support inclusion.
Compact uniform continuity of mixed derivatives then proves continuity of every
paired derivative. The fundamental theorem of calculus on parameter segments
bounds the fixed-support Taylor remainder by `‖h‖ ω(‖h‖)`, with `ω → 0`.
Applying the finite-order bound gives the real Fréchet derivative with
coefficients given by the paired parameter derivatives. Iterating this argument
gives smoothness and the formula for every `α`.

For a parameter test `φ`, put `β(p,y) = φ(p) * H(p,y)`. Its support is contained
in the compact product `tsupport φ × K`. The integration functional on `P` is
complex-linear and of order zero, since its norm is bounded by the enclosing
box volume times the supremum norm. The preceding smooth-family argument with
variables reversed proves smoothness of the integrated test `η`, its genuine
Lebesgue integrability at every `y`, and `tsupport η ⊆ K`. To exchange `T` and
integration, take finite grid Riemann sums of `β`. Every spatial derivative of
these sums converges uniformly, by compact uniform continuity on one enclosing
product box. Thus the sums converge in the fixed-support smooth topology and
then the canonical LF topology. Their pairings converge to `T η`; complex
linearity identifies the same pairings with scalar Riemann sums for `φ * G`.
This compactly supported continuous scalar function is genuinely integrable,
and its sums converge to the displayed integral. Uniqueness of the limit proves
the exchange formula. Empty `P`, `U`, or `K`, and zero `T` or `φ`, give zero
pairings or vacuous parameter assertions. No smoothness or derivative formula
for the paired function is included as a hypothesis. -/
theorem distribution_smooth_fixed_support_family
    {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (P : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k)))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K) (hKU : K ⊆ U)
    (H : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m) → ℂ)
    (hH : ContDiffOn ℝ ∞ (Function.uncurry H) ((P : Set _) ×ˢ (U : Set _)))
    (hSupport : ∀ p ∈ P, tsupport (H p) ⊆ K) :
    ∃ sections : EuclideanSpace ℝ (Fin k) → TestFunction U ℂ ⊤,
      (∀ p ∈ P, ∀ y, sections p y = H p y) ∧
      ContDiffOn ℝ ∞ (fun p ↦ T (sections p)) (P : Set _) ∧
      (∀ (α : Fin k → ℕ) (p : EuclideanSpace ℝ (Fin k)), p ∈ P →
        let directions := (List.finRange k).flatMap
          (fun i ↦ List.replicate (α i) (EuclideanSpace.single i (1 : ℝ)))
        ∃ differentiatedSection : TestFunction U ℂ ⊤,
          (∀ y, differentiatedSection y =
            iteratedFDerivWithin ℝ directions.length (fun q ↦ H q y) (P : Set _) p
              directions.get) ∧
          iteratedFDerivWithin ℝ directions.length (fun q ↦ T (sections q))
            (P : Set _) p directions.get = T differentiatedSection) ∧
      (∀ φ : TestFunction P ℂ ⊤,
        ∃ η : TestFunction U ℂ ⊤,
          (∀ y, IntegrableOn (fun p ↦ φ p * H p y) (P : Set _) volume) ∧
          (∀ y, η y = ∫ p in (P : Set _), φ p * H p y ∂volume) ∧
          tsupport (η : EuclideanSpace ℝ (Fin m) → ℂ) ⊆ K ∧
          IntegrableOn (fun p ↦ φ p * T (sections p)) (P : Set _) volume ∧
          T η = ∫ p in (P : Set _), φ p * T (sections p) ∂volume) := by
  classical
  have hExists (p : EuclideanSpace ℝ (Fin k)) (hp : p ∈ P) :
      ∃ f : TestFunction U ℂ ⊤, ∀ y, f y = H p y :=
    testFunction_of_contDiffOn_tsupport_subset hK hKU hH hp (hSupport p hp)
  let sections : EuclideanSpace ℝ (Fin k) → TestFunction U ℂ ⊤ :=
    fun p ↦ if hp : p ∈ P then (hExists p hp).choose else 0
  have hSections : ∀ p ∈ P, ∀ y, sections p y = H p y := by
    intro p hp y
    simp only [sections, dite_eq_left hp]
    exact (hExists p hp).choose_spec y
  obtain ⟨hSmooth, hDerivatives⟩ := distribution_pairing_smooth_on_fixed_support
    hm hk U P T K hK hKU H hH hSupport sections hSections
  refine ⟨sections, hSections, hSmooth, hDerivatives, ?_⟩
  intro φ
  exact distribution_pairing_integral_on_fixed_support
    hm hk U P T K hK hKU H hH hSupport sections hSections hSmooth.continuousOn φ

end HolomorphicAnosov.Analysis

