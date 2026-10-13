import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# kernel_regularized_pairing

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.D (3.26), p.27, passage between product integrals and current pairings; applied to I §3.E (3.29), p.28.
DAG node: `analysis.dbar_helper_kernel_regularized_pairing_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
If a scalar function has a kernel integral representation on an open parameter set, and the
product of one parameter test, the kernel and the scalar function is integrable on the product of
the restricted volume measures, then pairing the function with the parameter test equals pairing
it in the spatial variable with the integrated kernel test.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.D (3.26), p.27, passage between product integrals and current pairings; applied to I §3.E (3.29), p.28.

Proof/construction: Substitute the assumed kernel representation in the parameter integral. Move
the parameter test inside the spatial integral as a constant scalar factor and regroup
multiplication. The stated product-integrability hypothesis permits Fubini to exchange the
integrations. Move the spatial coefficient outside the parameter integral and use the definition
of the integrated test.
-/
theorem kernel_regularized_pairing {n : ℕ}
    (P Q : Opens (Fin n → ℂ)) (H : (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (φ : TestFunction P ℂ ⊤) (η f : (Fin n → ℂ) → ℂ)
    (hη : ∀ y, η y = ∫ p in (P : Set _), φ p * H p y)
    (hrepr : ∀ p ∈ P, f p = ∫ y in (Q : Set _), H p y * f y)
    (hint : Integrable (fun q : (Fin n → ℂ) × (Fin n → ℂ) ↦
      φ q.1 * H q.1 q.2 * f q.2)
      ((volume.restrict (P : Set _)).prod (volume.restrict (Q : Set _)))) :
    (∫ p in (P : Set _), f p * φ p) =
      ∫ y in (Q : Set _), f y * η y := by
  calc
    (∫ p in (P : Set _), f p * φ p) =
        ∫ p in (P : Set _), ∫ y in (Q : Set _), φ p * H p y * f y := by
      apply setIntegral_congr_fun P.isOpen.measurableSet
      intro p hp
      dsimp only
      rw [hrepr p hp, mul_comm, ← integral_const_mul]
      congr 1
      funext y
      ring
    _ = ∫ y in (Q : Set _), ∫ p in (P : Set _), φ p * H p y * f y :=
      integral_integral_swap hint
    _ = ∫ y in (Q : Set _), f y * η y := by
      apply integral_congr_ae
      filter_upwards with y
      rw [integral_mul_const, ← hη y, mul_comm]


end HolomorphicAnosov.Analysis.Distribution
