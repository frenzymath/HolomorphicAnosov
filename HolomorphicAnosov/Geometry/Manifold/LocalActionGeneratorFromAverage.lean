import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
An invertible spatial derivative of a fixed-time average determines the derivative of a local
action orbit at zero. (Bochner–Montgomery, Lemma 2, eqs. (14)–(17), pp. 688–689)
-/

open scoped Topology _root_.Topology
open MeasureTheory Filter

namespace HolomorphicAnosov

/-- An invertible derivative `B` of the fixed-time average gives the orbit derivative `B.symm (a h x
- a 0 x)` at zero. (Bochner–Montgomery, Lemma 2, eqs. (14)–(17), pp. 688–689) -/
theorem local_action_generator_from_average
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (a : ℝ → E → E) (x : E) (h : ℝ)
    (hint : IntervalIntegrable (fun t ↦ a t x) volume 0 h)
    (hmeas₀ : StronglyMeasurableAtFilter (fun t ↦ a t x) (𝓝 0))
    (hmeasₕ : StronglyMeasurableAtFilter (fun t ↦ a t x) (𝓝 h))
    (hcont₀ : ContinuousAt (fun t ↦ a t x) 0)
    (hcontₕ : ContinuousAt (fun t ↦ a t x) h)
    (B : E ≃L[ℝ] E)
    (haverage : HasFDerivAt (fun y ↦ ∫ t in 0..h, a t y)
      B.toContinuousLinearMap (a 0 x))
    (hcomp : ∀ᶠ p in 𝓝 (0 : ℝ), ∀ t ∈ Set.uIcc 0 h,
      a t (a p x) = a (t + p) x) :
    HasDerivAt (fun p ↦ a p x) (B.symm (a h x - a 0 x)) 0 := by
  have hd := intervalIntegral.integral_hasFDerivAt hint hmeas₀ hmeasₕ hcont₀ hcontₕ
  have hp : HasDerivAt (fun p : ℝ ↦ (p, h + p)) (1, 1) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk ((hasDerivAt_id (0 : ℝ)).const_add h)
  have hshift : HasDerivAt (fun p ↦ ∫ t in p..h + p, a t x)
      (a h x - a 0 x) 0 := by
    simpa [Function.comp_def] using hd.comp_hasDerivAt_of_eq 0 hp (by simp)
  have havg : HasDerivAt (fun p ↦ ∫ t in 0..h, a t (a p x))
      (a h x - a 0 x) 0 := by
    apply hshift.congr_of_eventuallyEq
    filter_upwards [hcomp] with p hp
    calc
      (∫ t in 0..h, a t (a p x)) = ∫ t in 0..h, a (t + p) x :=
        intervalIntegral.integral_congr hp
      _ = ∫ t in p..h + p, a t x := by
        simpa using intervalIntegral.integral_comp_add_right (a := 0) (b := h) (fun t ↦ a t x) p

  have hgen := HasFDerivAt.of_comp_of_leftInverse (f'symm := B.symm.toContinuousLinearMap)
    hcont₀ haverage havg.hasFDerivAt
    (Filter.EventuallyEq.rfl) B.symm_apply_apply
  simpa using hgen.hasDerivAt

end HolomorphicAnosov

