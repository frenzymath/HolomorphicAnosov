import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Order.ProjIcc

/-! Integrals of jointly continuous nonnegative speeds on compact intervals vary continuously with
parameters. (Lee, pp.275–279) -/

open Set MeasureTheory
open scoped Topology ENNReal

namespace HolomorphicAnosov

/-- The extended integral of a jointly continuous nonnegative speed on a fixed compact interval
depends continuously on the parameter. -/
theorem continuous_lintegral_compact_interval_speed
    {X : Type*} [TopologicalSpace X] {a b : ℝ} (hab : a ≤ b)
    (s : X × Icc a b → ℝ) (hs : Continuous s) (hs0 : ∀ z, 0 ≤ s z) :
    Continuous (fun x ↦ ∫⁻ t in Icc a b,
      ENNReal.ofReal (s (x, projIcc a b hab t))) := by
  let f : X → ℝ → ℝ := fun x t ↦ s (x, projIcc a b hab t)
  have hf : Continuous (Function.uncurry f) :=
    hs.comp (continuous_fst.prodMk (continuous_projIcc.comp continuous_snd))
  have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hf a b
  have heq (x : X) :
      ENNReal.ofReal (∫ t in a..b, f x t) =
        ∫⁻ t in Icc a b, ENNReal.ofReal (f x t) := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    exact ofReal_integral_eq_lintegral_ofReal
      ((hf.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc)
      (Filter.Eventually.of_forall (fun t ↦ hs0 (x, projIcc a b hab t)))
  exact (ENNReal.continuous_ofReal.comp hc).congr (fun x ↦ heq x)

end HolomorphicAnosov

