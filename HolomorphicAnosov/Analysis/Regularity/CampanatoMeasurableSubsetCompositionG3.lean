import HolomorphicAnosov.Analysis.Regularity.CampanatoAffineTransportG3
import HolomorphicAnosov.Analysis.Regularity.CampanatoAffineNormalizationEstimateG3
import HolomorphicAnosov.Analysis.Regularity.PolynomialAffineMixedPartialIdentityG3
import HolomorphicAnosov.Analysis.Regularity.EuclideanPolynomialMixedPartial
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace HolomorphicAnosov.Analysis.Regularity

/-- Campanato's remaining measurable-subset composition and affine scaling step.

Source: Campanato, *Proprietà di una famiglia di spazi funzionali*, Lemma [2.I],
pp.140--143, equations (2.7)--(2.12).  The supplied normalized coefficient
minimum is applied to the Borel representative of a null-measurable subset;
the affine map `y ↦ a + ρ y` transports both volume and the polynomial square,
and the finite mixed-partial coefficient identity converts the normalized
coefficient estimate into the displayed derivative bound.  This helper keeps
the exact public `NullMeasurableSet`, `volume.real`, classical mixed-partial,
and `Real.rpow` interfaces.  The missing formal composition of the admissible
weight minimum, completed-measure representative, affine change of variables,
and derivative normalization is retained as this named Stage 1 obligation.
-/
theorem campanato_measurable_subset_composition_g3
    (N n : ℕ) (hN : 1 ≤ N) (A : ℝ) (hA : 0 < A)
    (hAv : A ≤ volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1))
    (hlower :
      ∃ d : ℕ,
        ∃ e : (Fin d → ℝ) ≃ₗ[ℝ]
          ↥(MvPolynomial.restrictTotalDegree (Fin N) ℝ n),
        ∃ c : ℝ, 0 < c ∧
          ∀ v : Fin d → ℝ, v ∈ Metric.sphere (0 : Fin d → ℝ) 1 →
          ∀ E : Set (EuclideanSpace ℝ (Fin N)),
            NullMeasurableSet E volume →
            E ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1 →
            A ≤ volume.real E →
            c ≤ ∫ x in E,
              |MvPolynomial.eval (fun i ↦ x i) ((e v).val)| ^ 2) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (P : MvPolynomial (Fin N) ℝ) (a : EuclideanSpace ℝ (Fin N))
        (ρ : ℝ) (E : Set (EuclideanSpace ℝ (Fin N))),
        P.totalDegree ≤ n → 0 < ρ → NullMeasurableSet E volume →
        E ⊆ Metric.ball a ρ → A * ρ ^ N ≤ volume.real E →
        ∀ β : Fin N → ℕ, (∑ i, β i) ≤ n →
          |euclideanPolynomialMixedPartial P β a| ≤
            K * Real.rpow ρ (-((∑ i, β i) : ℝ) - (N : ℝ) / 2) *
              Real.sqrt (∫ y in E, |euclideanPolynomialEval P y| ^ 2) := by
  exact campanato_affine_normalization_estimate_g3 N n hN A hA hAv
    (fun a ρ f E hρ hE hf ↦ campanato_affine_setIntegral_transport_g3
      N a ρ f E hρ hE hf) hlower


end HolomorphicAnosov.Analysis.Regularity
