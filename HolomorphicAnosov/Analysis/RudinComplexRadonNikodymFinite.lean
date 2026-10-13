import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-!
# Complex Radon–Nikodym representation for a finite positive base measure

Source: Walter Rudin, *Real and Complex Analysis*, third edition (1987), Theorem 6.10,
printed pp. 121–123, especially the real/imaginary Jordan-variation reduction on p. 123.
The original measurable representative convention is Section 1.37, printed p. 29.

This module states DAG node `analysis.rudin_complex_radon_nikodym_finite`.
The proof follows the real and imaginary signed-measure reduction in the source.
-/

namespace HolomorphicAnosov

open MeasureTheory

/-- Rudin's complex Radon–Nikodym theorem for a finite positive base measure, on the original
sigma-algebra. The density is measurable and genuinely Bochner integrable. No completeness
of the measure space, topology on the source, or nonzero-measure assumption is imposed.

Source: Rudin, *Real and Complex Analysis*, third edition, Theorem 6.10, pp. 121–123;
Definitions 6.6–6.8, pp. 119–121; Theorem 6.4, pp. 118–119; Section 1.37, p. 29.

Natural-language proof (the complete proof of the corresponding DAG node):

1. Interpret `ν` as the genuine countably additive complex measure on the given sigma-algebra.
   Mathlib's `ComplexMeasure X` is `VectorMeasure X ℂ`; its values on nonmeasurable sets are
   zero by definition. The stated measurable-null-set assumption therefore gives vector
   absolute continuity with respect to `μ.toENNRealVectorMeasure`. Finite `μ` is sigma-finite.
   The real and imaginary continuous real-linear projections give signed measures `ν.re`
   and `ν.im` on this original measurable space.
2. Following Rudin's final paragraph on p. 123, apply the complex-component absolute-continuity
   equivalence to obtain absolute continuity of both signed parts with respect to this `μ`.
   Put `r = ν.re.rnDeriv μ` and `s = ν.im.rnDeriv μ`. The signed Radon–Nikodym theorem,
   which uses the positive-minus-negative Jordan variation formula, gives
   `μ.withDensityᵥ r = ν.re` and `μ.withDensityᵥ s = ν.im`.
3. Choose `h x = r x + Complex.I * s x`, namely `ν.rnDeriv μ`. The signed derivatives are
   measurable on the original sigma-algebra, so their complex recombination is measurable.
   The signed integrable-derivative theorems give integrability of `r` and `s`, and the complex
   integrable-derivative theorem gives genuine Bochner integrability of `h`. No completion of
   the sigma-algebra or extension on an arbitrary subset of a null set is used.
4. For a measurable `E`, evaluate the two signed density equalities using `withDensityᵥ_apply`
   and their integrability witnesses. This gives `ν.re E = ∫ x in E, r x ∂μ` and the analogous
   imaginary-part identity. Restriction preserves integrability of `h`. Apply
   `integral_re_add_im` for `μ.restrict E` to reconstruct `ν E = ∫ x in E, h x ∂μ`.
   This holds for every measurable `E`. If `μ = 0`, the null-set assumption forces `ν` to
   vanish on every measurable set and `h = 0` also works; if `ν = 0`, use `h = 0`.
-/
theorem rudin_complex_radon_nikodym_finite {X : Type*} [mX : MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (ν : ComplexMeasure X)
    (hν : ∀ E : Set X, MeasurableSet E → μ E = 0 → ν E = 0) :
    ∃ h : X → ℂ, Measurable h ∧ Integrable h μ ∧
      ∀ E : Set X, MeasurableSet E → ν E = ∫ x in E, h x ∂μ := by
  have h_ac : ν ≪ᵥ μ.toENNRealVectorMeasure := by
    intro E hE
    by_cases hEm : MeasurableSet E
    · exact hν E hEm (by simpa only [Measure.toENNRealVectorMeasure_apply_measurable hEm] using hE)
    · exact ν.not_measurable hEm
  obtain ⟨hre, him⟩ := (ν.absolutelyContinuous_ennreal_iff μ.toENNRealVectorMeasure).mp h_ac
  have hr := ν.re.withDensityᵥ_rnDeriv_eq μ hre
  have hi := ν.im.withDensityᵥ_rnDeriv_eq μ him
  refine ⟨ν.rnDeriv μ, ?_, ν.integrable_rnDeriv μ, ?_⟩
  · have hm := (Complex.continuous_ofReal.measurable.comp (ν.re.measurable_rnDeriv μ)).add
        ((Complex.continuous_ofReal.measurable.comp (ν.im.measurable_rnDeriv μ)).mul_const Complex.I)
    convert hm using 1
    funext x
    exact (Complex.re_add_im (ν.rnDeriv μ x)).symm
  · intro E hE
    have hrE : ν.re E = ∫ x in E, ν.re.rnDeriv μ x ∂μ :=
      (congrArg (fun s : SignedMeasure X ↦ s E) hr).symm.trans
        (withDensityᵥ_apply (ν.re.integrable_rnDeriv μ) hE)
    have hiE : ν.im E = ∫ x in E, ν.im.rnDeriv μ x ∂μ :=
      (congrArg (fun s : SignedMeasure X ↦ s E) hi).symm.trans
        (withDensityᵥ_apply (ν.im.integrable_rnDeriv μ) hE)
    calc
      ν E = (ν.re E : ℂ) + (ν.im E : ℂ) * Complex.I := (Complex.re_add_im (ν E)).symm
      _ = (↑(∫ x in E, ν.re.rnDeriv μ x ∂μ) : ℂ) +
          (↑(∫ x in E, ν.im.rnDeriv μ x ∂μ) : ℂ) * Complex.I := by rw [hrE, hiE]
      _ = ∫ x in E, ν.rnDeriv μ x ∂μ :=
        integral_re_add_im (ν.integrable_rnDeriv μ).integrableOn

end HolomorphicAnosov
